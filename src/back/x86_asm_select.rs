use std::collections::BTreeSet;
use std::fmt::{Display, Write};
use std::iter::zip;

use itertools::Itertools;
use regalloc2::{Edit, Inst, InstOrEdit, InstRange, MachineEnv, Operand, PReg, PRegSet, RegallocOptions, RegClass};
use regalloc2 as r2;
use regalloc2::VReg;

use crate::back::abi::{FunctionAbi, PassPosition};
use crate::back::layout::{Layout, TupleLayout};
use crate::back::register::{Register, RSize};
use crate::back::selector::{FunctionAbiId, Selector, Symbols, ValueMapper};
use crate::back::vcode::{AllocPos, AsmContext, InstInfo, StackLayout, VInstruction, VSymbol};
use crate::mid::analyse::usage::BlockUsage;
use crate::mid::analyse::use_info::UseInfo;
use crate::mid::ir::{BlockInfo, InstructionInfo, Program};
use crate::mid::normalize::split_critical_edges::split_critical_edges;
use crate::mid::util::verify::verify;
use crate::util::arena::{ArenaSet, IndexType};
use crate::util::internal_iter::InternalIterator;

pub fn lower_new(prog: &mut Program) -> String {
    // Builder::new().filter_level(LevelFilter::Trace).init();

    assert_eq!(prog.ptr_size_bits(), 64, "This backend only supports 64-bit");

    // the register allocator requires us to split critical edges
    // TODO merge edges without any moves again
    split_critical_edges(prog);
    verify(prog).unwrap();

    std::fs::write("pre_alloc.ir", format!("{}", prog)).unwrap();

    let use_info = UseInfo::new(prog);
    let mut symbols = Symbols::default();
    let mut abis: ArenaSet<FunctionAbiId, FunctionAbi> = ArenaSet::default();

    let mut output = Output::new(true);

    let main_func = *prog.root_functions.get("main").unwrap();
    output.appendln("main:");
    output.appendln(format_args!("    call func_{}", main_func.index()));
    output.appendln(format_args!("    mov rcx, rax"));
    output.appendln(format_args!("    call ExitProcess"));
    output.appendln("");

    for (func, _) in &prog.nodes.funcs {
        println!("Func {:?}", func);

        let func_info = prog.get_func(func);
        let mut mapper = ValueMapper::new(prog);

        let mut blocks = vec![];
        let mut v_instructions = vec![];

        // map blocks in-order
        let mut blocks_ordered = vec![];
        prog.reachable_blocks(func_info.entry).for_each(|block| {
            symbols.define_block(block, blocks_ordered.len());
            blocks_ordered.push(block);
        });

        // collect information about the code inside of this function
        let curr_func_abi_id = abis.push(FunctionAbi::for_type(prog, &func_info.func_ty));
        let mut large_block_params = vec![];
        let mut large_instrs = vec![];

        let mut inner_call_abis = vec![];

        for &block in &blocks_ordered {
            let block_info = &prog.get_block(block);

            if block != func_info.entry {
                for &param in &block_info.params {
                    if Layout::for_value(prog, param).reg_size().is_none() {
                        large_block_params.push(param);
                    }
                }
            }

            for &instr in &block_info.instructions {
                let instr_info = prog.get_instr(instr);

                if let Some(&target) = option_match!(instr_info, InstructionInfo::Call { target, args: _, conv: _ } => target) {
                    let ty = prog.type_of_value(target);
                    let func_ty = prog.get_type(ty).unwrap_func().unwrap();
                    let abi = FunctionAbi::for_type(prog, func_ty);

                    println!("{}", prog.format_type(ty));
                    println!("{:#?}", abi);

                    inner_call_abis.push(abis.push(abi));
                }

                if Layout::for_value(prog, instr).reg_size().is_none() {
                    large_instrs.push(instr);
                }
            }
        }

        // convert everything to vcode
        for &block in &blocks_ordered {
            let BlockInfo { params, instructions, terminator } = prog.get_block(block);

            // setup builder
            let range_start = v_instructions.len();
            let mut expr_cache = Default::default();
            let mut builder = Selector {
                prog,

                abis: &abis,
                curr_func_abi: &abis[curr_func_abi_id],
                curr_func_abi_id,

                symbols: &mut symbols,
                values: &mut mapper,
                instructions: &mut v_instructions,
                expr_cache: &mut expr_cache,
            };

            let vreg_params = if block == func_info.entry {
                // allocate stack at the start of the function
                builder.push(VInstruction::StackAlloc);

                // define function params for entry block as defs instead of block params
                for (index, &param) in params.iter().enumerate() {
                    match abis[curr_func_abi_id].pass_params[index].pos {
                        PassPosition::Reg(param_reg) => {
                            let param = builder.values.map_param(param).as_small().unwrap();
                            builder.push(VInstruction::DefFixedReg(param, param_reg));
                        }
                        PassPosition::StackSlot(_) => {}
                    }
                }
                vec![]
            } else {
                // define standard block params that fit into registers as virtual block params
                params.iter()
                    .filter_map(|&param| builder.values.map_param(param).as_small())
                    .collect_vec()
            };

            // convert instructions to vcode
            for &instr in instructions {
                builder.append_instr(instr);
            }
            builder.append_terminator(terminator);

            // construct block
            let range_end = v_instructions.len();
            let inst_range = InstRange::forward(Inst::new(range_start), Inst::new(range_end));

            let succs = terminator.successors().map(|succ| symbols.map_block(succ)).collect_vec();
            let preds = use_info[block].iter().filter_map(|usage| {
                match usage {
                    BlockUsage::FuncEntry(_) => None,
                    BlockUsage::Target { pos, kind: _ } => Some(symbols.map_block(pos.block))
                }
            }).collect();

            blocks.push(R2BlockInfo { inst_range, succs, preds, params: vreg_params });
        };

        let inst_infos = v_instructions.iter().map(|inst| inst.to_inst_info()).collect();

        let func_wrapper = FuncWrapper {
            entry_block: symbols.map_block(func_info.entry),
            blocks,
            v_instructions,
            inst_infos,
            vregs: mapper.vreg_count(),
        };

        // TODO use more registers
        let env = build_env(4);
        let options = RegallocOptions {
            verbose_log: false,
            validate_ssa: true,
        };

        println!();
        println!();
        println!();
        let result = r2::run(&func_wrapper, &env, &options).unwrap();
        println!("{:?}", result);

        // TODO save and restore used callee-saved registers
        // TODO ensure stack is aligned to max(inner_call_abi.align, slot_values.align) assuming only curr_abi.align
        //    and don't forget to properly restore the stack pointer at the end!

        // TODO we don't _really_ need params & instrs to be aligned, we never take their address anyway
        // we don't need space for large params & returns in calls since we can just use the space for their values
        let mut slot_layouts = vec![];
        slot_layouts.extend(func_info.slots.iter().map(|&slot| Layout::for_value(prog, slot)));
        slot_layouts.extend(large_block_params.iter().map(|&param| Layout::for_value(prog, param)));
        slot_layouts.extend(large_instrs.iter().map(|&instr| Layout::for_value(prog, instr)));

        println!("slot_layouts:");
        for layout in &slot_layouts {
            println!("  {:?}", layout);
        }

        let slot_layout = TupleLayout::from_layouts(slot_layouts.iter().copied());

        // reserve space for the largest call necessary
        let max_call_space = inner_call_abis.iter()
            .map(|&abi| abis[abi].stack_space_allocated_by_caller)
            .max().unwrap_or(0);

        let mut offsets = slot_layout.offsets.iter().map(|&o| o + max_call_space).collect_vec();
        offsets.reverse();

        let slot_offsets = func_info.slots.iter().map(|&slot| (slot, offsets.pop().unwrap())).collect();
        let param_offsets = large_block_params.iter().map(|&slot| (slot, offsets.pop().unwrap())).collect();
        let instr_offsets = large_instrs.iter().map(|&slot| (slot, offsets.pop().unwrap())).collect();

        let curr_func_abi = &abis[curr_func_abi_id];

        let stack_layout = StackLayout {
            alloc_bytes: RSize::FULL.bytes() + slot_layout.layout.size_bytes + max_call_space,
            free_bytes: curr_func_abi.stack_space_freed_by_callee,
            slot_offsets,
            param_offsets,
            instr_offsets,
        };

        let mut ctx = AsmContext {
            prog,
            allocs: Default::default(),
            stack_layout,
        };

        // actually generate code
        output.appendln(format_args!("{}:", VSymbol::Global(func.into()).to_asm(&ctx)));

        for &block in &blocks_ordered {
            let block_r2 = symbols.map_block(block);
            output.appendln(format_args!("  {}:", VSymbol::Block(block).to_asm(&ctx)));

            for inst in result.block_insts_and_edits(&func_wrapper, block_r2) {
                match inst {
                    InstOrEdit::Inst(inst) => {
                        let v_inst = &func_wrapper.v_instructions[inst.index()];

                        let inst_allocs = result.inst_allocs(inst);
                        let inst_operands = &func_wrapper.inst_infos[inst.index()].operands;
                        assert_eq!(inst_allocs.len(), inst_operands.len());

                        ctx.allocs.clear();
                        for (&operand, &alloc) in zip(inst_operands, inst_allocs) {
                            ctx.allocs.insert(operand.vreg(), alloc);
                        }

                        output.append_v_inst(v_inst, &ctx);
                    }
                    InstOrEdit::Edit(edit) => {
                        let &Edit::Move { from, to } = edit;

                        let to = AllocPos::from(to);
                        let from = AllocPos::from(from);

                        output.comment(format_args!("    ; {:?}", edit));
                        output.appendln(format_args!("    mov {}, {}", to.to_asm(RSize::FULL), from.to_asm(RSize::FULL)));
                    }
                }
            }
        }

        output.appendln("");
    }

    output.finish(prog).unwrap()
}

struct Output {
    text: String,
    comments: bool,
}

impl Output {
    fn new(comments: bool) -> Self {
        Output {
            text: String::new(),
            comments,
        }
    }

    fn comment(&mut self, f: impl Display) {
        if self.comments {
            self.appendln(f);
        }
    }

    fn appendln(&mut self, f: impl Display) {
        writeln!(&mut self.text, "{}", f).unwrap();
    }

    fn append_v_inst(&mut self, v_inst: &VInstruction, ctx: &AsmContext) {
        self.comment(format_args!("    ; {:?} {:?}", v_inst, ctx.allocs));

        // moves that should be skipped get "none" as operands
        if ctx.allocs.values().any(|a| a.is_none()) {
            assert!(v_inst.to_inst_info().is_move.is_some());
            return;
        }

        // append the actual code
        let result = v_inst.to_asm(ctx);
        for line in result.lines() {
            self.appendln(format_args!("    {}", line.trim()));
        }
    }

    fn finish(self, prog: &Program) -> Result<String, std::fmt::Error> {
        let mut ext_set: BTreeSet<&str> = prog.nodes.exts.iter().map(|(_, ext_info)| ext_info.name.as_str()).collect();
        ext_set.insert("ExitProcess");

        let mut result = String::new();
        let f = &mut result;

        writeln!(f, "global main")?;

        for ext in ext_set {
            writeln!(f, "extern {}", ext)?;
        }
        writeln!(f, "\n")?;

        writeln!(f, "section .text")?;
        writeln!(f, "{}", self.text)?;

        writeln!(f, "section .data")?;
        for (data, data_info) in &prog.nodes.datas {
            write!(f, "data_{}:\n  db ", data.index())?;
            for (i, b) in data_info.bytes.iter().enumerate() {
                if i != 0 { write!(f, ", ")? }
                write!(f, "{}", b)?;
            }
            writeln!(f)?;
        }

        Ok(result)
    }
}

fn build_env(reg_count: usize) -> MachineEnv {
    // don't use stack pointer as general purpose register
    let mut regs = Register::ALL.iter()
        .filter(|&&reg| reg != Register::SP)
        .map(|reg| PReg::new(reg.index(), RegClass::Int))
        .collect_vec();

    drop(regs.drain(reg_count..));

    MachineEnv {
        preferred_regs_by_class: [regs, vec![]],
        non_preferred_regs_by_class: [vec![], vec![]],
        // TODO use fixed stack slots for params and return values
        fixed_stack_slots: vec![],
    }
}

struct FuncWrapper {
    entry_block: r2::Block,
    blocks: Vec<R2BlockInfo>,
    v_instructions: Vec<VInstruction>,
    inst_infos: Vec<InstInfo>,
    vregs: usize,
}

struct R2BlockInfo {
    inst_range: InstRange,
    succs: Vec<r2::Block>,
    preds: Vec<r2::Block>,
    params: Vec<VReg>,
}

impl r2::Function for FuncWrapper {
    fn num_insts(&self) -> usize {
        self.inst_infos.len()
    }

    fn num_blocks(&self) -> usize {
        self.blocks.len()
    }

    fn entry_block(&self) -> r2::Block {
        self.entry_block
    }

    fn block_insns(&self, block: r2::Block) -> InstRange {
        self.blocks[block.0 as usize].inst_range
    }

    fn block_succs(&self, block: r2::Block) -> &[r2::Block] {
        &self.blocks[block.0 as usize].succs
    }

    fn block_preds(&self, block: r2::Block) -> &[r2::Block] {
        &self.blocks[block.0 as usize].preds
    }

    fn block_params(&self, block: r2::Block) -> &[VReg] {
        &self.blocks[block.0 as usize].params
    }

    fn is_ret(&self, inst: Inst) -> bool {
        self.inst_infos[inst.0 as usize].is_ret
    }

    fn is_branch(&self, inst: Inst) -> bool {
        self.inst_infos[inst.0 as usize].is_branch
    }

    fn branch_blockparams(&self, _: r2::Block, inst: Inst, succ_idx: usize) -> &[VReg] {
        let info = &self.inst_infos[inst.0 as usize];
        assert!(info.is_branch);
        &info.branch_block_params[succ_idx]
    }

    fn is_move(&self, inst: Inst) -> Option<(Operand, Operand)> {
        self.inst_infos[inst.0 as usize].is_move
    }

    fn inst_operands(&self, inst: Inst) -> &[Operand] {
        &self.inst_infos[inst.0 as usize].operands
    }

    fn inst_clobbers(&self, inst: Inst) -> PRegSet {
        self.inst_infos[inst.0 as usize].clobbers
    }

    fn num_vregs(&self) -> usize {
        self.vregs
    }

    fn spillslot_size(&self, _: RegClass) -> usize {
        // TODO figure out what this is
        1
    }
}
