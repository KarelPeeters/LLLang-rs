use std::cmp::Ordering;
use std::collections::HashMap;

use itertools::Itertools;

use crate::mid::analyse::dom_info::DomInfo;
use crate::mid::analyse::use_info::UseInfo;
use crate::mid::ir::{Block, ComparisonOp, ExpressionInfo, Function, Global, Immediate, Program, Scoped, Terminator, Value};
use crate::util::internal_iter::{InternalIterator, IterExt};

pub fn cond_prop(prog: &mut Program) -> bool {
    let use_info = UseInfo::new(prog);
    let mut replaced = 0;

    for func in prog.nodes.funcs.keys().collect_vec() {
        replaced += cond_prop_func(prog, func, &use_info);
    }

    println!("conv_prop replaced {} values", replaced);
    replaced != 0
}

// TODO expand to more conditional cases, eg if we know `a == b` then we also know `a > b`.
fn cond_prop_func(prog: &mut Program, func: Function, use_info: &UseInfo) -> usize {
    let mut replaced = 0;

    let dom_info = DomInfo::new(prog, func);
    for &block in dom_info.blocks() {
        let mut simplify = HashMap::new();

        // TODO this is weird, we should really do this as a tree structure instead of repeatedly visiting the same
        //   parent blocks over and over
        let dom_tree = dom_info.iter_domtree(block).collect_vec();

        // iterate top-down so we can immediately use the parent known values
        for &dominator in dom_tree.iter().rev() {
            // if all predecessors agree
            // TODO this flatten stuff is a bit weird
            let pair = dom_info.iter_predecessors(dominator).map(|pred| {
                sorted_pair_for_block_edge(prog, &simplify, pred, dominator)
            }).single_unique().flatten();

            if let Some(SimplifyPair { complex, simple }) = pair {
                simplify.insert(complex, simple);
            }
        }

        println!("Known values for block {:?}: {:?}", block, simplify);

        // replace values used in the current block
        // TODO replace expression operands (clone if necessary, and write util for this in use_info)
        for (&complex, &simple) in &simplify {
            // replacement dominance should be fine,
            //   since the new value comes from a parent block that by definition dominates this block
            replaced += use_info.replace_value_usages_if(prog, complex, simple, |prog, usage| {
                usage.as_dom_pos().map_or(false, |pos| pos.block() == Some(block))
            });
        }

        // TODO replace target values within branch that has eq thing, maybe just as a separate step?
    }

    replaced
}

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
struct SimplifyPair {
    complex: Value,
    simple: Value,
}

fn sorted_pair_for_block_edge(prog: &Program, simplify: &HashMap<Value, Value>, parent: Block, child: Block) -> Option<SimplifyPair> {
    if let Terminator::Branch { cond, ref true_target, ref false_target } = prog.get_block(parent).terminator {
        if let Some(cond) = cond.as_expr() {
            if let &ExpressionInfo::Comparison { kind, left, right} = prog.get_expr(cond) {
                if implies_operands_eq(kind, true_target.block, false_target.block, child) {
                    let left = *simplify.get(&left).unwrap_or(&left);
                    let right = *simplify.get(&right).unwrap_or(&right);
                    return sort_pair(prog, left, right);
                }
            }
        }
    }

    None
}

fn implies_operands_eq(kind: ComparisonOp, true_block: Block, false_block: Block, child: Block) -> bool {
    match (child == true_block, child == false_block) {
        (false, false) => unreachable!("child block is neither true nor false, which means it's not a descendant!"),
        (true, false) => kind == ComparisonOp::Eq,
        (false, true) => kind == ComparisonOp::Neq,
        (true, true) => false,
    }
}

fn sort_pair(prog: &Program, left: Value, right: Value) -> Option<SimplifyPair> {
    match value_complexity(prog, left).cmp(&value_complexity(prog, right)) {
        Ordering::Less => Some(SimplifyPair  { complex: right, simple: left } ),
        Ordering::Greater => Some(SimplifyPair { complex: left, simple: right }),
        Ordering::Equal => None,
    }
}

// TODO move this to common analysis infrastructure
fn value_complexity(prog: &Program, value: Value) -> u32 {
    match value {
        Value::Immediate(Immediate::Undef(_)) => 0,
        Value::Immediate(Immediate::Void) => 0,

        Value::Immediate(Immediate::Const(_)) => 1,

        // order doesn't matter here, they shouldn't really be considered together anyway
        Value::Global(Global::Func(_)) => 2,
        Value::Global(Global::Extern(_)) => 2,
        Value::Global(Global::Data(_)) => 2,

        // prefer slot so local analysis can see more
        Value::Scoped(Scoped::Slot(_)) => 2,
        Value::Scoped(Scoped::Param(_)) => 3,

        // sort expression by tree size
        // TODO consider type of expression, eg. multiply is worse than add
        Value::Expr(expr) => {
            10 + prog.expr_tree_iter(expr).count() as u32
        }

        // instructions are terrible
        Value::Scoped(Scoped::Instr(_)) => u32::MAX,
    }
}