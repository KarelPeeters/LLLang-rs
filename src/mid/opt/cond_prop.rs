use std::cmp::Ordering;
use std::collections::HashMap;

use itertools::Itertools;

use crate::mid::analyse::dom_info::DomInfo;
use crate::mid::analyse::usage::{TargetKind, TermOperand, Usage};
use crate::mid::analyse::use_info::UseInfo;
use crate::mid::ir::{Block, ComparisonOp, ExpressionInfo, Function, Global, Immediate, Program, Scoped, Terminator, Value};
use crate::mid::opt::runner::{PassContext, PassResult, ProgramPass};
use crate::util::internal_iter::InternalIterator;

#[derive(Debug)]
pub struct CondPropPass;

impl ProgramPass for CondPropPass {
    fn run(&self, prog: &mut Program, ctx: &mut PassContext) -> PassResult {
        let use_info = ctx.use_info(prog);
        let mut replaced = 0;

        for func in prog.nodes.funcs.keys().collect_vec() {
            let dom_info = ctx.dom_info(prog, func);
            replaced += cond_prop_func(prog, func, &use_info, &dom_info);
        }

        println!("conv_prop replaced {} values", replaced);

        let changed = replaced != 0;
        PassResult {
            changed,
            preserved_dom_info: true,
            preserved_use_info: !changed,
        }
    }

    fn is_idempotent(&self) -> bool {
        // TODO is it? can we easily make it?
        false
    }
}

#[derive(Debug, Copy, Clone)]
struct Replacement {
    complex: Value,
    simple: Value,

    cond: ReplacementCondition,
}

#[derive(Debug, Copy, Clone)]
struct ReplacementCondition {
    block: Block,
    true_block: Block,
    false_block: Block,
    branch: bool,
}

impl ReplacementCondition {
    fn applies_to_instr_in(&self, dom_info: &DomInfo, block: Block) -> bool {
        match self.branch {
            true => dom_info.is_dominator(self.true_block, block) && !dom_info.is_reachable(self.false_block, block),
            false => dom_info.is_dominator(self.false_block, block) && !dom_info.is_reachable(self.true_block, block),
        }
    }

    fn applies_to_branch_in(&self, block: Block, branch: bool) -> bool {
        block == self.block && branch == self.branch
    }
}

// TODO expand to more conditional cases, eg if we know `a == b` then we also know `a > b`.
fn cond_prop_func(prog: &mut Program, func: Function, use_info: &UseInfo, dom_info: &DomInfo) -> usize {
    // collect replacement values
    let mut replacements = vec![];

    for &block in dom_info.blocks() {
        if let &Terminator::Branch { cond, ref true_target, ref false_target } = &prog.get_block(block).terminator {
            if let Some(cond) = cond.as_expr() {
                if let &ExpressionInfo::Comparison { kind, left, right } = prog.get_expr(cond) {
                    let eq_for_target = match kind {
                        ComparisonOp::Eq => Some(true),
                        ComparisonOp::Neq => Some(false),
                        _ => None,
                    };

                    // TODO already simplify cond, left and right

                    if let Some(eq_for_target) = eq_for_target {
                        if let Some(pair) = sort_pair(prog, left, right) {
                            replacements.push(Replacement {
                                complex: pair.complex,
                                simple: pair.simple,
                                cond: ReplacementCondition {
                                    block,
                                    true_block: true_target.block,
                                    false_block: false_target.block,
                                    branch: eq_for_target,
                                },
                            })
                        }
                    }
                }
            }
        }
    }

    // todo for a certain block, find the set of simplest replacements that apply
    if !replacements.is_empty() {
        println!("Replacements:");
        for r in &replacements {
            println!("  {:?}", r);
        }
    }

    // apply replacements
    let mut replaced = 0;

    for replacement in replacements {
        // TODO only apply replacement if it's the simplest one that applies

        replaced += use_info.replace_value_usages_if(prog, replacement.complex, replacement.simple, |prog, usage| {
            match usage {
                Usage::RootFunction(_) => false,
                // TODO support replacing  expression operands
                Usage::ExprOperand { .. } => false,

                Usage::InstrOperand { pos, usage } =>
                    replacement.cond.applies_to_instr_in(&dom_info, pos.block),

                Usage::TermOperand { pos, usage } => {
                    match usage {
                        TermOperand::BranchCond | TermOperand::ReturnValue =>
                            replacement.cond.applies_to_instr_in(&dom_info, pos.block),
                        TermOperand::TargetArg { kind, index: _ } => {
                            match kind {
                                TargetKind::Jump =>
                                    replacement.cond.applies_to_instr_in(&dom_info, pos.block),
                                TargetKind::BranchTrue =>
                                    replacement.cond.applies_to_branch_in(pos.block, true),
                                TargetKind::BranchFalse =>
                                    replacement.cond.applies_to_branch_in(pos.block, false),
                            }
                        }
                    }
                }
            }
        });
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
            if let &ExpressionInfo::Comparison { kind, left, right } = prog.get_expr(cond) {
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
        Ordering::Less => Some(SimplifyPair { complex: right, simple: left }),
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

        // ordered by how easy it is for analysis to reason about
        // the exact order is probably not that important, these should rarely be compared
        Value::Global(Global::Data(_)) => 2,
        Value::Global(Global::Func(_)) => 2,
        Value::Scoped(Scoped::Slot(_)) => 3,
        Value::Scoped(Scoped::Param(_)) => 4,
        Value::Global(Global::Extern(_)) => 5,

        // sort expression by tree size
        // TODO consider type of expression, eg. multiply is worse than add
        Value::Expr(expr) => {
            let operand_count = prog.expr_tree_iter(expr).count() as u32;
            let max_operand_complexity = prog.expr_tree_leaf_iter(expr).map(|(leaf, _, _)| value_complexity(prog, leaf)).max().unwrap_or(0);
            10 + max_operand_complexity + operand_count
        }

        // instructions are terrible
        Value::Scoped(Scoped::Instr(_)) => u32::MAX / 2,
    }
}