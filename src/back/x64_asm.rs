use std::cmp::max;
use std::collections::HashMap;
use itertools::Itertools;

use regalloc2 as r2;
use regalloc2::{Inst, InstRange, Operand, PRegSet, RegClass, VReg};

use crate::back::x64_calling_convention::{ArgPosition, CallLayout};
use crate::mid::analyse::dom_info::DomInfo;
use crate::mid::analyse::use_info::UseInfo;
use crate::mid::ir::{Block, Function, Instruction, InstructionInfo, Phi, Program, Value};
use crate::mid::normalize::remove_entry_phis::remove_entry_phis;
use crate::mid::normalize::split_critical_edges::split_critical_edges;

pub fn lower(prog: &mut Program) -> String {
    // normalize
    remove_entry_phis(prog);
    split_critical_edges(prog);
    // TODO replace function params and returns that are too large with pointers

    let mut builder = ProgramBuilder::new(prog);
    let use_info = UseInfo::new(prog);
    let ctx = Context { prog, use_info: &use_info };

    for func in use_info.funcs() {
        lower_func(ctx, &mut builder, func);
    }

    builder.finish()
}

fn lower_func(ctx: Context, builder: &mut ProgramBuilder, func: Function) {
    let prog = ctx.prog;
    let use_info = ctx.use_info;
    let dom_info = DomInfo::new(prog, func);
    let func_info = prog.get_func(func);


    assert!(func_info.entry.phi_values.is_empty());

    let blocks: HashMap<Block, r2::Block> = use_info.func_blocks(func).iter().enumerate().map(|(i, &b)| {
        let result = r2::Block::new(i);
        println!("Mapping {:?} -> {:?}", b, result);
        (b, result)
    }).collect();

    let mut mapper = Mapper::new(blocks);
    let mut instrs = vec![];
    let mut blocks = vec![];

    for &block in use_info.func_blocks(func) {
        let inst_start_index = instrs.len();

        // map phis
        let phis = prog.get_block(block).phis.iter().map(|&phi| mapper.map_phi(phi)).collect_vec();

        // map params for the entry block
        if block == func_info.entry.block {
            assert!(phis.is_empty());
            assert!(instrs.is_empty());

            let layout = CallLayout::for_func(prog, func).unwrap();
            for pos in layout.params {
                match pos {
                    ArgPosition::Register(_) => {}
                    ArgPosition::Stack { .. } => {}
                }
            }
        }

        // map instructions
        for &instr in &prog.get_block(block).instructions {
            let instr_info = prog.get_instr(instr);
            match instr_info {
                InstructionInfo::Load { .. } => {}
                InstructionInfo::Store { .. } => {}
                InstructionInfo::Call { .. } => {}
                InstructionInfo::Arithmetic { .. } => {}
                InstructionInfo::Comparison { .. } => {}
                InstructionInfo::TupleFieldPtr { .. } => {}
                InstructionInfo::PointerOffSet { .. } => {}
                InstructionInfo::Cast { .. } => {}
                InstructionInfo::BlackBox { .. } => {}
            }
        }

        // map terminator

        // finish block
        let inst_end_index = instrs.len();
        let inst_range = InstRange::forward(Inst::new(inst_start_index), Inst::new(inst_end_index));

        let mut succs = vec![];
        prog.get_block(block).terminator.for_each_successor(|succ| succs.push(mapper.map_block(succ)));
        let preds = dom_info.iter_predecessors(block).map(|pred| mapper.map_block(pred)).collect();

        let info = R2BlockInfo { inst_range, succs, preds, params: phis };
        blocks.push(info);
    }

    // allocate registers

    // encode instructions

    todo!()
}

pub struct Mapper {
    blocks: HashMap<Block, r2::Block>,

    next_vreg: usize,
    values: HashMap<Value, VReg>,
}

impl Mapper {
    fn new(blocks: HashMap<Block, r2::Block>) -> Self {
        Mapper {
            blocks,
            next_vreg: 0,
            values: Default::default(),
        }
    }

    fn map_block(&self, block: Block) -> r2::Block {
        *self.blocks.get(&block).unwrap()
    }

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

    fn new_dummy(&mut self, value: Value, instrs: &mut Vec<InstInfo>) -> VReg {
        let reg = self.new_vreg();

        println!("{:?} <- dummy {:?} ({:?})", Inst::new(instrs.len()), value, reg);

        instrs.push(InstInfo {
            is_ret: false,
            is_branch: false,
            is_move: None,
            operands: vec![Operand::reg_def(reg)],
            clobbers: PRegSet::empty(),
            branch_blockparams: vec![],
        });

        reg
    }

    fn map_value(&mut self, value: Value) -> Option<VReg> {
        match value {
            Value::Void | Value::Undef(_) | Value::Const(_) | Value::Func(_) |
            Value::Slot(_) | Value::Extern(_) | Value::Data(_) => {
                // these typically don't require an actual register
                // TODO put params in registers
                None
            }
            Value::Param(_) => {
                // params should have been mapped at the start of the function
                Some(*self.values.get(&value).unwrap())
            }
            Value::Phi(_) | Value::Instr(_) => {
                let next_vreg = &mut self.next_vreg;
                Some(*self.values.entry(value).or_insert_with(|| {
                    let index = *next_vreg;
                    *next_vreg += 1;
                    let reg = VReg::new(index, RegClass::Int);

                    println!("Mapping {:?} to {:?}", value, reg);
                    reg
                }))
            }
        }
    }

    fn map_value_or_dummy(&mut self, value: Value, instrs: &mut Vec<InstInfo>) -> VReg {
        self.map_value(value).unwrap_or_else(|| self.new_dummy(value, instrs))
    }
}

#[derive(Copy, Clone)]
struct Context<'a> {
    prog: &'a Program,
    use_info: &'a UseInfo,
}

#[derive(Debug, Copy, Clone)]
pub enum Register {
    RAX,
    RBX,
    RCX,
    RDX,
    RSI,
    RDI,
    RBP,
    RSP,
    R8,
    R9,
    R10,
    R11,
    R12,
    R13,
    R14,
    R15,
}

pub const RETURN_REGISTER: Register = Register::RAX;
pub const PARAM_REGISTERS: &[Register] = &[Register::RCX, Register::RDX, Register::R8, Register::R9];

pub const VOLATILE_REGISTERS: &[Register] = &[Register::RAX, Register::RCX, Register::RDX, Register::R8, Register::R9, Register::R10, Register::R11];

struct ProgramBuilder<'a> {
    prog: &'a Program,
}

impl<'a> ProgramBuilder<'a> {
    pub fn new(prog: &'a Program) -> Self {
        Self { prog }
    }

    pub fn finish(self) -> String {
        todo!()
    }
}

struct FuncStackLayoutEarly {
    stack_space_real_slots: i32,
    // stack_space_spill_slots: i32, // TODO we don't know this yet
    stack_space_max_call: i32,
}

impl FuncStackLayoutEarly {
    fn new(ctx: Context, func: Function) -> Self {
        let prog = ctx.prog;
        let use_info = ctx.use_info;

        // figure out how much stack space we need for the biggest call
        let mut stack_space_max_call = 0;
        for &block in use_info.func_blocks(func) {
            for &instr in &prog.get_block(block).instructions {
                let instr_info = prog.get_instr(instr);
                if let &InstructionInfo::Call { target, .. } = instr_info {
                    let ty = prog.get_type(prog.type_of_value(target)).unwrap_func().unwrap();
                    let layout = CallLayout::new(prog, ty).unwrap();
                    stack_space_max_call = max(stack_space_max_call, layout.stack_param_area);
                }
            }
        }

        // allocate stack size for the stack slots
        //TODO
        //  maybe do this after register allocation?

        FuncStackLayoutEarly {
            stack_space_real_slots: todo!(),
            stack_space_max_call,
        }
    }
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

struct FuncWrapper {
    entry_block: r2::Block,
    blocks: Vec<R2BlockInfo>,
    insts: Vec<InstInfo>,
    vregs: usize,
    block_map: HashMap<Block, r2::Block>,
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
