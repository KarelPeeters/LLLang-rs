use std::collections::HashSet;
use crate::mid::analyse::dom_info::DomInfo;
use crate::mid::analyse::use_info::UseInfo;
use crate::mid::ir::{Block, Program};
use crate::util::internal_iter::InternalIterator;

pub fn replace_large_values(prog: &mut Program) {
    let use_info = UseInfo::new(prog);

    for func in use_info.funcs() {
        let dom_info = DomInfo::new(prog, func);
        let entry = prog.get_func(func).entry;

        let mut edges_to_visit = HashSet::new();

        for &block in use_info.func_blocks(func) {
            // TODO assert that there are no critical edges

            if block != entry {
                // check for incoming edge
                // TODO
            }

            // check for outgoing edge
            if let Some((target, target_kind)) = prog.get_block(block).terminator.targets().single() {
                let edge = Edge { from: block, to: target.block };
                edges_to_visit.remove(&edge);

                // TODO handle edge
            } else {
                // hopefully we'll visit them later
                prog.get_block(block).terminator.successors().for_each(|succ| {
                    edges_to_visit.insert(Edge { from:block, to: succ });
                })
            }
        }

        assert!(edges_to_visit.is_empty(), "Leftover edges in {:?}: {:?}", func, edges_to_visit);
    }
}

#[derive(Debug, Copy, Clone, Hash, Eq, PartialEq)]
pub struct Edge {
    from: Block,
    to: Block,
}
