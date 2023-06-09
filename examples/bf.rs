use std::iter::Peekable;
use std::path::{Path, PathBuf};
use std::process::Command;

use clap::Clap;
use itertools::Itertools;

use lllang::back;
use lllang::mid::ir::{ArithmeticOp, Block, BlockInfo, CallingConvention, CastKind, ComparisonOp, Const, Expression, ExpressionInfo, Extern, ExternInfo, FunctionInfo, FunctionType, InstructionInfo, ParameterInfo, Program, Signed, StackSlot, StackSlotInfo, Target, Terminator, Type, Value};
use lllang::mid::ir::Signed::Unsigned;
use lllang::mid::opt::runner::{PassRunner, RunnerChecks, RunnerSettings};
use lllang::mid::util::bit_int::{BitInt, UStorage};
use lllang::mid::util::verify::verify;
use lllang::tools::{render_ir_as_svg, run_link, run_nasm};

#[derive(Clap, Debug)]
pub struct Args {
    #[clap(long)]
    memory_size: usize,

    source: String,
}

fn main() {
    let args = Args::parse();

    println!("Parsing program");
    let mut prog = build_prog(&args.source, args.memory_size);

    let output = PathBuf::from("ignored/bf/");
    std::fs::create_dir_all(&output).unwrap();

    println!("Writing before");
    std::fs::write(output.join("bf_before.ir"), format!("{}", prog)).unwrap();
    render_ir_as_svg(&prog, output.join("bf_before.svg")).unwrap();

    println!("Optimizing program");
    verify(&prog).unwrap();
    run_optimizations(&mut prog);

    println!("Writing after");
    render_ir_as_svg(&prog, output.join("bf_after.svg")).unwrap();
    std::fs::write(output.join("bf_after.ir"), format!("{}", prog)).unwrap();

    verify(&prog).unwrap();
    run_prog(&mut prog, &output);
}

fn run_prog(prog: &mut Program, folder: &Path) {
    println!("Generating assembly");
    let asm = back::x86_asm_select::lower_new(prog);

    let asm_path = folder.join("bf.asm");
    let obj_path = folder.join("bf.obj");
    let exe_path = folder.join("bf.exe");

    println!("Assembling");
    std::fs::write(&asm_path, &asm).unwrap();
    assert!(run_nasm(&asm_path, &obj_path).unwrap().success());

    println!("Linking");
    assert!(run_link(&obj_path, &exe_path).unwrap().success());

    println!("Running");
    let result = Command::new(exe_path).status().unwrap();
    println!("{}", result);
}

fn build_prog(source: &str, memory_size: usize) -> Program {
    let mut prog = Program::new(64);

    let ty_ptr = prog.ty_ptr();
    let ty_byte = prog.define_type_int(8);
    let ty_u32 = prog.define_type_int(32);
    let ty_int = prog.define_type_int(64);
    let zero_int = Const::new(ty_int, BitInt::zero(64));

    // function used for codegen
    let func_ty = FunctionType {
        params: vec![ty_ptr],
        ret: ty_byte,
        conv: CallingConvention::Custom,
    };

    let func_info = FunctionInfo::new(func_ty, &mut prog);
    let entry = func_info.entry;
    let param_addr = prog.get_block_mut(entry).params[0];

    let func = prog.define_func(func_info);

    let slot = prog.define_slot(StackSlotInfo { inner_ty: ty_int, debug_name: Some("index".to_owned()) });
    prog.get_func_mut(func).slots.push(slot);

    let store = prog.define_instr(InstructionInfo::Store {
        addr: slot.into(),
        ty: ty_int,
        value: zero_int.into(),
    });
    prog.get_block_mut(entry).instructions.push(store);

    let mut chars = source.chars().peekable();
    let final_block = parse(&mut prog, entry, param_addr.into(), slot, &mut chars);
    assert!(chars.next().is_none());

    let ret = Terminator::Return { value: Const::new(ty_byte, BitInt::zero(8)).into() };
    set_terminator(&mut prog, final_block, ret);

    // main function that just calls the codegen function
    let main_func_info = FunctionInfo::new(FunctionType {
        params: vec![],
        ret: ty_int,
        conv: CallingConvention::Win64,
    }, &mut prog);
    let mut block = main_func_info.entry;
    let main_func = prog.define_func(main_func_info);

    // set yup the buffer
    let external = add_external_functions(&mut prog);

    let heap = prog.define_instr(InstructionInfo::Call {
        target: external.get_process_heap.into(),
        args: vec![],
        conv: CallingConvention::Win64,
    });
    let base = prog.define_instr(InstructionInfo::Call {
        target: external.heap_alloc.into(),
        args: vec![
            heap.into(),
            Const::new(ty_u32, BitInt::zero(32)).into(),
            Const::new(ty_int, BitInt::from_unsigned(64, memory_size as UStorage).unwrap()).into(),
        ],
        conv: CallingConvention::Win64,
    });
    let free = prog.define_instr(InstructionInfo::Call {
        target: external.heap_free.into(),
        args: vec![
            heap.into(),
            Const::new(ty_u32, BitInt::zero(32)).into(),
            base.into(),
        ],
        conv: CallingConvention::Win64,
    });

    prog.get_block_mut(block).instructions.push(heap);
    prog.get_block_mut(block).instructions.push(base);

    block = zero_memory(&mut prog, block, base.into(), memory_size);

    let call = prog.define_instr(InstructionInfo::Call {
        target: func.into(),
        args: vec![base.into()],
        conv: CallingConvention::Custom,
    });
    prog.get_block_mut(block).instructions.push(call);

    prog.get_block_mut(block).instructions.push(free);

    let cast = prog.define_expr(ExpressionInfo::Cast {
        ty: ty_int,
        kind: CastKind::IntExtend(Signed::Unsigned),
        value: call.into(),
    });
    set_terminator(&mut prog, block, Terminator::Return { value: cast.into() });

    prog.root_functions.insert("main".to_owned(), main_func);

    prog
}

struct ExternalFunctions {
    get_process_heap: Extern,
    heap_alloc: Extern,
    heap_free: Extern,
}

fn zero_memory(prog: &mut Program, block_start: Block, base: Value, length: usize) -> Block {
    let ty_int = prog.define_type_int(64);
    let ty_byte = prog.define_type_int(8);

    let const_int_one = Const::new(ty_int, BitInt::from_unsigned(64, 1).unwrap());
    let const_int_zero = Const::new(ty_int, BitInt::zero(64));
    let const_int_length = Const::new(ty_int, BitInt::from_unsigned(64, length as UStorage).unwrap());
    let const_byte_zero = Const::new(ty_byte, BitInt::zero(8));

    // build blocks
    let block_body = prog.define_block(BlockInfo::new());
    let block_cond = prog.define_block(BlockInfo::new());
    let block_end = prog.define_block(BlockInfo::new());

    // build expressions and instructions
    let curr_i = prog.define_param(ParameterInfo { ty: ty_int });
    prog.get_block_mut(block_cond).params.push(curr_i);

    let offset = prog.define_expr(ExpressionInfo::PointerOffSet {
        ty: ty_byte,
        base,
        index: curr_i.into(),
    });
    let store = prog.define_instr(InstructionInfo::Store {
        addr: offset.into(),
        ty: ty_byte,
        value: const_byte_zero.into(),
    });
    let next_i = prog.define_expr(ExpressionInfo::Arithmetic {
        kind: ArithmeticOp::Add,
        ty: ty_int,
        left: curr_i.into(),
        right: const_int_one.into(),
    });
    let cond = prog.define_expr(ExpressionInfo::Comparison {
        kind: ComparisonOp::Lt(Unsigned),
        left: curr_i.into(),
        right: const_int_length.into(),
    });

    prog.get_block_mut(block_body).instructions.push(store);

    // connect terminators
    set_terminator(prog, block_start, Terminator::Jump { target: Target { block: block_cond, args: vec![const_int_zero.into()] } });
    set_terminator(prog, block_cond, Terminator::Branch { cond: cond.into(), true_target: target(block_body), false_target: target(block_end) });
    set_terminator(prog, block_body, Terminator::Jump { target: Target { block: block_cond, args: vec![next_i.into()] } });

    block_end
}

fn add_external_functions(prog: &mut Program) -> ExternalFunctions {
    let ty_ptr = prog.ty_ptr();
    let ty_dword = prog.define_type_int(32);
    let ty_size = prog.define_type_int(64);

    let get_process_heap_ty = prog.define_type_func(FunctionType {
        params: vec![],
        ret: ty_ptr,
        conv: CallingConvention::Win64,
    });
    let heap_alloc_ty = prog.define_type_func(FunctionType {
        params: vec![ty_ptr, ty_dword, ty_size],
        ret: ty_ptr,
        conv: CallingConvention::Win64,
    });
    let heap_free_ty = prog.define_type_func(FunctionType {
        params: vec![ty_ptr, ty_dword, ty_ptr],
        ret: ty_dword,
        conv: CallingConvention::Win64,
    });
    ExternalFunctions {
        get_process_heap: prog.define_ext(ExternInfo {
            name: "GetProcessHeap".to_owned(),
            ty: get_process_heap_ty,
        }),
        heap_alloc: prog.define_ext(ExternInfo {
            name: "HeapAlloc".to_owned(),
            ty: heap_alloc_ty,
        }),
        heap_free: prog.define_ext(ExternInfo {
            name: "HeapFree".to_owned(),
            ty: heap_free_ty,
        }),
    }
}

// TODO extract some of the program building logic into a common module, used by both LL and BF
//   eg. load, store, while loop, push instruction to block, ...
fn parse(prog: &mut Program, start: Block, data_base: Value, data_index: StackSlot, left: &mut Peekable<impl Iterator<Item=char>>) -> Block {
    let ty_ptr = prog.ty_ptr();
    let ty_byte = prog.define_type_int(8);
    let ty_int = prog.define_type_int(64);
    let cst_byte_one = Const::new(ty_int, BitInt::from_unsigned(8, 1).unwrap());
    let cst_int_one = Const::new(ty_int, BitInt::from_unsigned(64, 1).unwrap());

    let mut block = start;

    loop {
        if left.peek() == Some(&']') {
            // hopefully end of the loop, let the caller handle it
            break;
        }

        let curr_char = match left.next() {
            Some(c) => c,
            None => break,
        };

        match curr_char {
            '>' => increment_addr(prog, block, data_index.into(), ty_int, ArithmeticOp::Add),
            '<' => increment_addr(prog, block, data_index.into(), ty_int, ArithmeticOp::Sub),
            '+' => {
                let ptr = data_ptr(prog, block, data_base, data_index);
                increment_addr(prog, block, ptr.into(), ty_byte, ArithmeticOp::Add);
            }
            '-' => {
                let ptr = data_ptr(prog, block, data_base, data_index);
                increment_addr(prog, block, ptr.into(), ty_byte, ArithmeticOp::Sub);
            }
            '.' => {
                let ptr = data_ptr(prog, block, data_base, data_index);
                let value = prog.define_instr(InstructionInfo::Load {
                    addr: ptr.into(),
                    ty: ty_byte,
                });

                let block_info = prog.get_block_mut(block);
                block_info.instructions.push(value);

                // TODO actually output to stdout instead of returning
                set_terminator(prog, block, Terminator::Return { value: value.into() });

                // continue parsing code in new block
                block = prog.define_block(BlockInfo::new());
            }
            ',' => {
                // TODO actually get stdin input instead of a constant 0xff
                let ptr = data_ptr(prog, block, data_base, data_index);
                let store = prog.define_instr(InstructionInfo::Store {
                    addr: ptr.into(),
                    ty: ty_byte,
                    value: Const::new(ty_byte, BitInt::from_unsigned(8, 0xff).unwrap()).into(),
                });
                prog.get_block_mut(block).instructions.push(store);
            }
            '[' => {
                let block_cond = prog.define_block(BlockInfo::new());
                let block_body_start = prog.define_block(BlockInfo::new());

                // condition
                let data_ptr = data_ptr(prog, block_cond, data_base, data_index);
                let load_data = prog.define_instr(InstructionInfo::Load {
                    addr: data_ptr.into(),
                    ty: ty_byte,
                });
                prog.get_block_mut(block_cond).instructions.push(load_data);
                let cond = prog.define_expr(ExpressionInfo::Comparison {
                    kind: ComparisonOp::Neq,
                    left: load_data.into(),
                    right: Const::new(ty_byte, BitInt::zero(8)).into(),
                });

                // block codegen
                let block_body_end = parse(prog, block_body_start, data_base, data_index, left);
                let option = left.next();
                assert!(option == Some(']'), "unmatched '['");

                // connect everything together
                let block_end = prog.define_block(BlockInfo::new());

                set_terminator(prog, block, Terminator::Jump { target: target(block_cond) });
                set_terminator(prog, block_cond, Terminator::Branch {
                    cond: cond.into(),
                    true_target: target(block_body_start),
                    false_target: target(block_end),
                });
                set_terminator(prog, block_body_end, Terminator::Jump { target: target(block_cond) });

                block = block_end;
            }
            ']' => unreachable!("handled earlier"),
            _ => {
                // ignore other characters
            }
        }
    }

    block
}

fn target(block: Block) -> Target {
    Target {
        block,
        args: vec![],
    }
}

fn set_terminator(prog: &mut Program, block: Block, term: Terminator) {
    let block_info = prog.get_block_mut(block);
    assert!(matches!(block_info.terminator, Terminator::Unreachable));
    block_info.terminator = term;
}

fn increment_addr(prog: &mut Program, block: Block, addr: Value, ty: Type, kind: ArithmeticOp) {
    let bits = prog.get_type(ty).unwrap_int().unwrap();
    let cst_one = Const::new(ty, BitInt::from_unsigned(bits, 1).unwrap());

    let load = prog.define_instr(InstructionInfo::Load {
        addr,
        ty,
    });
    let add = prog.define_expr(ExpressionInfo::Arithmetic {
        kind,
        ty,
        left: load.into(),
        right: cst_one.into(),
    });
    let store = prog.define_instr(InstructionInfo::Store {
        addr,
        ty,
        value: add.into(),
    });

    let instructions = &mut prog.get_block_mut(block).instructions;
    instructions.push(load);
    instructions.push(store);
}

fn data_ptr(prog: &mut Program, block: Block, base: Value, index: StackSlot) -> Expression {
    let ty_byte = prog.define_type_int(8);
    let ty_int = prog.define_type_int(64);

    let load_index = prog.define_instr(InstructionInfo::Load {
        addr: index.into(),
        ty: ty_int,
    });
    prog.get_block_mut(block).instructions.push(load_index);
    let offset = prog.define_expr(ExpressionInfo::PointerOffSet {
        ty: ty_byte,
        base,
        index: load_index.into(),
    });
    offset
}

fn run_optimizations(prog: &mut Program) {
    let settings = RunnerSettings {
        max_loops: None,
        checks: RunnerChecks::all(),
        // TODO configurable logging
        log_path_ir: None,
        log_path_svg: None,
    };

    let runner = PassRunner::with_default_passes(settings);
    runner.run(prog).unwrap();
}