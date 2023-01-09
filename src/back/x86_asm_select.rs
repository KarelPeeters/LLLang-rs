use std::fmt::{Display, Write};
use std::iter::zip;

use env_logger::Builder;
use itertools::Itertools;
use log::LevelFilter;
use regalloc2::{Edit, Inst, InstOrEdit, InstRange, MachineEnv, Operand, PRegSet, RegallocOptions, RegClass};
use regalloc2 as r2;
use regalloc2::VReg;

use crate::back::selector::{Selector, Symbols, VRegMapper};
use crate::back::vcode::{ABI_PARAM_REGS, AsmContext, GENERAL_PREGS, InstInfo, Size, StackLayout, VInstruction, VRegPos, VSymbol};
use crate::mid::analyse::usage::BlockUsage;
use crate::mid::analyse::use_info::UseInfo;
use crate::mid::ir::{BlockInfo, Program};
use crate::mid::normalize::split_critical_edges::split_critical_edges;
use crate::mid::util::verify::verify;
use crate::util::{Never, NeverExt};

pub fn lower_new(prog: &mut Program) -> String {
    Builder::new().filter_level(LevelFilter::Trace).init();

    // the register allocator requires us to split critical edges
    // TODO merge edges without any moves again
    split_critical_edges(prog);
    verify(prog).unwrap();

    std::fs::write("pre_alloc.ir", format!("{}", prog)).unwrap();

    let use_info = UseInfo::new(prog);
    let mut symbols = Symbols::default();

    let mut output = Output::new(true);

    let main_func = *prog.root_functions.get("main").unwrap();
    output.appendln("_main:");
    output.appendln(format_args!("    call {}", VSymbol::Global(main_func.into())));
    output.appendln(format_args!("    push eax"));
    output.appendln(format_args!("    call _ExitProcess@4"));
    output.appendln("");

    for (func, _) in &prog.nodes.funcs {
        println!("Func {:?}", func);

        let func_info = prog.get_func(func);
        let mut mapper = VRegMapper::default();

        let mut blocks = vec![];
        let mut v_instructions = vec![];

        // map blocks in-order
        let mut blocks_ordered = vec![];
        prog.try_visit_blocks(func_info.entry, |block| {
            symbols.define_block(block, blocks_ordered.len());
            blocks_ordered.push(block);
            Never::UNIT
        }).no_err();

        // map slots
        let slots = func_info.slots.iter().enumerate().map(|(i, &slot)| (slot, i)).collect();

        for &block in &blocks_ordered {
            println!("  Block {:?} -> {:?}", block, symbols.map_block(block).0);
            let BlockInfo { params, instructions, terminator } = prog.get_block(block);

            // setup builder
            let mut params = params.iter().map(|&param| mapper.map_param(param)).collect_vec();
            println!("    params {:?}", params);

            let range_start = v_instructions.len();
            let mut builder = Selector {
                prog,
                symbols: &mut symbols,
                vregs: &mut mapper,
                slots: &slots,
                instructions: &mut v_instructions,
                expr_cache: &mut Default::default(),
            };

            if block == func_info.entry {
                // allocate stack at the start of the function
                builder.push(VInstruction::StackAlloc);

                // define function params for entry block as defs instead of block params
                for (index, &param) in params.iter().enumerate() {
                    // TODO use the proper ABI registers
                    let preg = ABI_PARAM_REGS[index];
                    builder.push(VInstruction::DefFixedReg(param, preg));
                }
                params.clear();
            }

            // convert instructions to vcode
            for &instr in instructions {
                builder.append_instr(instr);
            }
            builder.append_terminator(terminator);

            // construct block
            let range_end = v_instructions.len();
            let inst_range = InstRange::forward(Inst::new(range_start), Inst::new(range_end));

            let mut succs = vec![];
            terminator.for_each_successor(|succ| succs.push(symbols.map_block(succ)));
            let preds = use_info[block].iter().filter_map(|usage| {
                match usage {
                    BlockUsage::FuncEntry(_) => None,
                    BlockUsage::Target { pos, kind: _ } => Some(symbols.map_block(pos.block))
                }
            }).collect();

            println!("  succs: {:?}", succs);

            blocks.push(R2BlockInfo { inst_range, succs, preds, params });
        };

        let inst_infos = v_instructions.iter().map(|inst| inst.to_inst_info()).collect();

        let func_wrapper = FuncWrapper {
            entry_block: symbols.map_block(func_info.entry),
            blocks,
            v_instructions,
            inst_infos,
            vregs: mapper.vreg_count(),
        };

        let env = build_env(4);
        let options = RegallocOptions {
            verbose_log: true,
            validate_ssa: true,
        };

        println!();
        println!();
        println!();
        let result = r2::run(&func_wrapper, &env, &options).unwrap();
        println!("{:?}", result);

        // TODO do all of this properly, depending on the calling convention
        let stack_layout = StackLayout {
            slot_bytes: slots.len() * 4,
            spill_bytes: result.num_spillslots,
            param_bytes: 0,
        };
        let mut ctx = AsmContext {
            allocs: Default::default(),
            stack_layout,
        };

        // actually generate code
        output.appendln(format_args!("{}:", VSymbol::Global(func.into())));

        for &block in &blocks_ordered {
            let block_r2 = symbols.map_block(block);
            output.appendln(format_args!("  {}:", VSymbol::Block(block)));

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

                        let to = VRegPos::from(to);
                        let from = VRegPos::from(from);

                        output.comment(format_args!("    ; {:?}", edit));
                        output.appendln(format_args!("    mov {}, {}", to.to_asm(Size::FULL), from.to_asm(Size::FULL)));
                    }
                }
            }
        }

        output.appendln("\n");
    }

    // TODO extern symbols
    // TODO _main
    // => single func, no slots, simple loops should start working

    // TODO stack management
    // TODO call arg pushing
    // => func calls should start working

    // TODO proper register sizing
    // TODO managing larger-than reg values
    // => everything should be working

    output.finish()
}

struct Output {
    header: String,
    text: String,
    comments: bool,
}

impl Output {
    fn new(comments: bool) -> Self {
        Output {
            header: String::new(),
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

    fn finish(self) -> String {
        format!("global _main\nextern _ExitProcess@4\n{}\n\nsection .text\n{}", self.header, self.text)
    }
}

fn build_env(reg_count: usize) -> MachineEnv {
    let regs = GENERAL_PREGS[..reg_count].to_vec();
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
