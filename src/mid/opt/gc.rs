use crate::mid::ir::{Program, Function};

pub fn gc(prog: &mut Program) {
    let use_info = usage_info(prog);

}

struct UseInfo {

}

fn usage_info(prog: &Program) {
    //TODO write this out manually once, then maybe look into generating code for it
    //   (something like #derive(User))
}