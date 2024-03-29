use lllang::front;
use lllang::front::pos::FileId;
use lllang::mid::ir::{Block, Function, FunctionInfo, FunctionType, Parameter, Program};

pub fn parse_ir_standalone(source: &str) -> Program {
    let mut prog_module = front::Program::new(64);
    let module = prog_module.find_or_create_module(vec!["main".to_owned()]);

    // parse
    let content = front::parser::parse_module(FileId(0), source).unwrap();
    module.content = Some(content);

    // resolve
    let prog_resolved = front::resolve::resolve(&prog_module).unwrap();

    // lower
    let prog_ir = front::lower::lower(prog_resolved).unwrap();

    prog_ir
}

pub fn get_debug_func(prog: &Program, name: &str) -> Function {
    let mut cands = vec![];
    prog.nodes.funcs.keys().find(|&func| {
        let func_info = prog.get_func(func);
        if let Some(curr_name) = &func_info.debug_name {
            cands.push(curr_name);
        }
        func_info.debug_name.as_deref() == Some(name)
    })
        .unwrap_or_else(|| {
            panic!("Count not find function {:?}, candidates are: {:?}", name, cands);
        })
}

// TODO support slots?
// TODO is this useful, or should we just have a parsable ir representation?
#[allow(dead_code)]
pub fn generate_test_func(mut prog: Program, ty: FunctionType, generate: impl FnOnce(&mut Program, Block, Vec<Parameter>)) -> Program {
    let info = FunctionInfo::new(ty, &mut prog);
    let params = prog.get_block(info.entry).params.clone();

    generate(&mut prog, info.entry, params);

    let func = prog.define_func(info);
    prog.root_functions.insert("test".to_owned(), func);

    prog
}