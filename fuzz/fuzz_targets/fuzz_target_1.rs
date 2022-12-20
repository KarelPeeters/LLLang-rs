#![no_main]

use libfuzzer_sys::{Corpus, fuzz_target};
use lllang::front;
use lllang::front::pos::FileId;
use std::collections::HashMap;

fuzz_target!(|data: &str| -> Corpus {
    if !data.is_ascii() {
        return Corpus::Reject;
    }

    let mut counter = HashMap::<char, u32>::new();
    for c in data.chars() {
        if !c.is_whitespace() {
            *counter.entry(c).or_default() += 1;
        }
    }
    if counter.values().any(|&v| v > 32) {
        return Corpus::Reject;
    }

    let mut prog_module = front::Program::default();
    let module = prog_module.find_or_create_module(vec!["main".to_owned()]);

    // parse
    let content = match front::parser::parse_module(FileId(0), data) {
        Ok(content) => content,
        Err(_) => return Corpus::Reject,
    };
    module.content = Some(content);

    // resolve
    let prog_resolved = match front::resolve::resolve(&prog_module) {
        Ok(prog_resolved) => prog_resolved,
        Err(_) => return Corpus::Reject,
    };

    // lower
    let prog_ir = match front::lower::lower(prog_resolved) {
        Ok(prog_ir) => prog_ir,
        Err(_) => return Corpus::Reject,
    };

    Corpus::Keep

    // panic!("Successfully lowered to IR program!")
});
