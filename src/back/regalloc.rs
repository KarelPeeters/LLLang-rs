use std::collections::HashMap;

use itertools::Itertools;
use regalloc2 as r2;
use regalloc2::{Inst, InstOrEdit, InstRange, MachineEnv, Operand, PReg, PRegSet, RegallocOptions, RegClass, VReg};

use crate::mid::analyse::dom_info::DomInfo;
use crate::mid::analyse::use_info::{for_each_usage_in_instr, UseInfo};
use crate::mid::ir::{Block, Function, Instruction, InstructionInfo, Phi, Program, Target, Terminator, Value};
use crate::mid::normalize::remove_entry_phis::remove_entry_phis;
use crate::mid::normalize::split_critical_edges::split_critical_edges;

pub fn test_regalloc(prog: &mut Program) {
    // normalize and cast to immutable
    remove_entry_phis(prog);
    split_critical_edges(prog);
    let prog = &*prog;

    let use_info = UseInfo::new(prog);

    for func in use_info.funcs() {
        let wrapper = FuncWrapper::new(prog, func, &use_info);

        let reg_count = 8;
        let regs = (0..reg_count).map(|i| PReg::new(i, RegClass::Int)).collect_vec();

        let env = MachineEnv {
            preferred_regs_by_class: [regs, vec![]],
            non_preferred_regs_by_class: [vec![], vec![]],
            fixed_stack_slots: vec![],
        };

        let options = RegallocOptions {
            verbose_log: true,
            validate_ssa: true,
        };

        // Builder::new().filter_level(LevelFilter::Trace).init();
        let result = r2::run(&wrapper, &env, &options).unwrap();
        println!("{:?}", result);

        println!("Generated code:");
        println!("{:?}", use_info);

        for &block in use_info.func_blocks(func) {
            println!("  {:?}:", block);
            for item in result.block_insts_and_edits(&wrapper, *wrapper.block_map.get(&block).unwrap()) {
                match item {
                    InstOrEdit::Inst(inst) => println!("    {:?} {:?}", inst, result.inst_allocs(inst)),
                    InstOrEdit::Edit(edit) => println!("    {:?}", edit),
                }
            }
        }
    }
}

// TODO try clobbering something for fun
// TODO try reusing a register (eg in arithmetic)

#[derive(Default)]
struct Mapper {
    next_vreg: usize,
    value_map: HashMap<Value, VReg>,
}

impl Mapper {
    fn new_vreg(&mut self) -> VReg {
        let index = self.next_vreg;
        self.next_vreg += 1;
        VReg::new(index, RegClass::Int)
    }

    fn map_phi(&mut self, phi: Phi) -> VReg {
        self.map_value(phi.into()).unwrap()
    }

    fn map_instr(&mut self, instr: Instruction) -> VReg {
        self.map_value(instr.into()).unwrap()
    }

    fn map_value(&mut self, value: Value) -> Option<VReg> {
        match value {
            Value::Void | Value::Undef(_) | Value::Const(_) | Value::Func(_) |
            Value::Param(_) | Value::Slot(_) | Value::Extern(_) | Value::Data(_) => {
                // these typically don't require an actual register
                // TODO put params in registers
                None
            }
            Value::Phi(_) | Value::Instr(_) => {
                let next_vreg = &mut self.next_vreg;
                Some(*self.value_map.entry(value).or_insert_with(|| {
                    let index = *next_vreg;
                    *next_vreg += 1;
                    let reg = VReg::new(index, RegClass::Int);

                    println!("Mapping {:?} to {:?}", value, reg);
                    reg
                }))
            }
        }
    }
}

impl FuncWrapper {
    fn new(prog: &Program, func: Function, _: &UseInfo) -> Self {
        let dom_info = DomInfo::new(prog, func);

        let block_map: HashMap<Block, r2::Block> = dom_info.blocks.iter().enumerate().map(|(i, &b)| {
            let result = r2::Block::new(i);
            println!("Mapping {:?} -> {:?}", b, result);
            (b, result)
        }).collect();
        let map_block = |block: Block| -> r2::Block { *block_map.get(&block).unwrap() };

        let mut instrs = vec![];
        let mut blocks = vec![];
        let mut mapper = Mapper::default();

        for &block in &dom_info.blocks {
            assert_eq!(blocks.len(), map_block(block).index());

            let inst_start = instrs.len();

            // map phis
            let phis = prog.get_block(block).phis.iter().map(|&phi| mapper.map_phi(phi)).collect();

            // append instructions
            for &instr in &prog.get_block(block).instructions {
                let mut operands = vec![];
                let mut clobbers = PRegSet::empty();

                let instr_info = prog.get_instr(instr);
                let output_reg = mapper.map_instr(instr);

                match instr_info {
                    &InstructionInfo::Arithmetic { kind, left, right } => {
                        let left_reg = mapper.map_value(left).unwrap();
                        let right_reg = mapper.map_value(right);

                        operands.push(Operand::reg_reuse_def(output_reg, 1));
                        operands.push(Operand::reg_use(left_reg));
                        if let Some(right_reg) = right_reg {
                            operands.push(Operand::reg_use(right_reg));
                        }
                    }
                    _ => {
                        operands.push(Operand::reg_def(output_reg));
                        for_each_usage_in_instr((), instr_info, |value, _| {
                            if let Some(value_reg) = mapper.map_value(value) {
                                operands.push(Operand::reg_use(value_reg));
                            }
                        });
                    }
                }

                let info = InstInfo {
                    is_ret: false,
                    is_branch: false,
                    is_move: None,
                    operands,
                    clobbers,
                    branch_blockparams: vec![],
                };

                println!("{:?} <- {:?}", Inst::new(instrs.len()), instr);

                instrs.push(info);
            }

            // push terminator as inst
            {
                let mut has_target = false;
                let mut operands = vec![];
                let mut phi_args = vec![];

                let mut add_target = |t: &Target| {
                    has_target = true;
                    phi_args.push(t.phi_values.iter().map(|&phi_value| {
                        mapper.map_value(phi_value).unwrap_or_else(|| {
                            let reg = mapper.new_vreg();

                            println!("{:?} <- phi_value {:?}", Inst::new(instrs.len()), phi_value);

                            // define dummy store instruction
                            instrs.push(InstInfo {
                                is_ret: false,
                                is_branch: false,
                                is_move: None,
                                operands: vec![Operand::reg_def(reg)],
                                clobbers: PRegSet::empty(),
                                branch_blockparams: vec![],
                            });
                            reg
                        })
                    }).collect());
                };

                let term = &prog.get_block(block).terminator;
                match term {
                    Terminator::Jump { target } => add_target(target),
                    &Terminator::Branch { cond, ref true_target, ref false_target } => {
                        add_target(true_target);
                        add_target(false_target);

                        if let Some(cond_reg) = mapper.map_value(cond) {
                            operands.push(Operand::reg_use(cond_reg));
                        }
                    }
                    &Terminator::Return { value } => {
                        if let Some(value_reg) = mapper.map_value(value) {
                            operands.push(Operand::reg_use(value_reg));
                        }
                    }
                    Terminator::Unreachable => {}
                }

                let info = InstInfo {
                    is_ret: !has_target,
                    is_branch: has_target,
                    is_move: None,
                    operands,
                    clobbers: PRegSet::empty(),
                    branch_blockparams: phi_args,
                };

                println!("{:?} <- {:?}", Inst::new(instrs.len()), term);

                instrs.push(info);
            }

            // finalize block
            let inst_end = instrs.len();
            let inst_range = InstRange::forward(Inst::new(inst_start), Inst::new(inst_end));

            let mut succs = vec![];
            prog.get_block(block).terminator.for_each_successor(|succ| succs.push(map_block(succ)));

            let preds = dom_info.iter_predecessors(block).map(map_block).collect();

            let info = R2BlockInfo { inst_range, succs, preds, params: phis };
            blocks.push(info);
        }

        FuncWrapper {
            entry_block: map_block(prog.get_func(func).entry.block),
            blocks,
            insts: instrs,
            vregs: mapper.next_vreg,
            mapper,
            block_map,
        }
    }
}

struct FuncWrapper {
    entry_block: r2::Block,
    blocks: Vec<R2BlockInfo>,
    insts: Vec<InstInfo>,
    vregs: usize,

    block_map: HashMap<Block, r2::Block>,
    mapper: Mapper,
}

struct InstInfo {
    // ret/unreachable -> ret
    is_ret: bool,
    // jump/branch -> branch
    is_branch: bool,

    // TODO figure out when this should be set, maybe for stack loads/stores?
    is_move: Option<(Operand, Operand)>,
    operands: Vec<Operand>,
    clobbers: PRegSet,

    branch_blockparams: Vec<Vec<VReg>>,
}

struct R2BlockInfo {
    inst_range: InstRange,
    succs: Vec<r2::Block>,
    preds: Vec<r2::Block>,
    params: Vec<VReg>,
}

impl r2::Function for FuncWrapper {
    fn num_insts(&self) -> usize {
        self.insts.len()
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
        self.insts[inst.0 as usize].is_ret
    }

    fn is_branch(&self, inst: Inst) -> bool {
        self.insts[inst.0 as usize].is_branch
    }

    fn branch_blockparams(&self, _: r2::Block, inst: Inst, succ_idx: usize) -> &[VReg] {
        &self.insts[inst.0 as usize].branch_blockparams[succ_idx]
    }

    fn is_move(&self, inst: Inst) -> Option<(Operand, Operand)> {
        self.insts[inst.0 as usize].is_move
    }

    fn inst_operands(&self, inst: Inst) -> &[Operand] {
        &self.insts[inst.0 as usize].operands
    }

    fn inst_clobbers(&self, inst: Inst) -> PRegSet {
        self.insts[inst.0 as usize].clobbers
    }

    fn num_vregs(&self) -> usize {
        self.vregs
    }

    fn spillslot_size(&self, _: RegClass) -> usize {
        // TODO figure out what this is
        1
    }
}
