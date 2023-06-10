use std::cmp::Ordering;

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

    cond: Condition,
}

#[derive(Debug, Copy, Clone)]
struct Branch {
    block: Block,
    true_block: Block,
    false_block: Block,
}

#[derive(Debug, Copy, Clone)]
struct Condition {
    branch: Branch,
    cond: bool,
}

impl Condition {
    fn applies_to_instr_in(&self, dom_info: &DomInfo, block: Block) -> bool {
        match self.cond {
            true => dom_info.is_dominator(self.branch.true_block, block) && !dom_info.is_reachable(self.branch.false_block, block),
            false => dom_info.is_dominator(self.branch.false_block, block) && !dom_info.is_reachable(self.branch.true_block, block),
        }
    }

    fn applies_to_target_in_branch(&self, block: Block, cond: bool) -> bool {
        block == self.branch.block && cond == self.cond
    }
}

#[derive(Default)]
struct Replacements {
    replacements: Vec<Replacement>,
}

impl Replacements {
    fn maybe_push_eq(&mut self, prog: &Program, branch: Branch, cond: bool, left: Value, right: Value) {
        if let Some(pair) = sort_pair(prog, left, right) {
            self.replacements.push(Replacement {
                complex: pair.complex,
                simple: pair.simple,
                cond: Condition {
                    branch,
                    cond,
                },
            })
        }
    }

    fn maybe_push_comparison(&mut self, prog: &Program, branch: Branch, kind: ComparisonOp, left: Value, right: Value) {
        // TODO is all this extra complexity not unnecessary once we have bool expression simplification?
        if prog.type_of_value(left) == prog.ty_bool() {
            if let Some(right) = right.as_const().map(|c| c.as_bool().unwrap()) {
                // comparison to boolean constant, we can add a lot of info from this
                match kind {
                    ComparisonOp::Eq => {
                        self.maybe_push_eq(prog, branch, true, left, prog.const_bool(right).into());
                        self.maybe_push_eq(prog, branch, false, left, prog.const_bool(!right).into());
                    }
                    ComparisonOp::Neq => {
                        self.maybe_push_eq(prog, branch, true, left, prog.const_bool(!right).into());
                        self.maybe_push_eq(prog, branch, false, left, prog.const_bool(right).into());
                    }
                    _ => {}
                }

                // we don't need to add the less complete replacements later
                return;
            }
        }

        // push replacement resulting from equality comparison
        match kind {
            ComparisonOp::Eq => self.maybe_push_eq(prog, branch, true, left, right),
            ComparisonOp::Neq => self.maybe_push_eq(prog, branch, false, left, right),
            _ => {}
        }
    }
}

// TODO simplify cond, left and right following other replacements?
//    we can't just do that here, we need to visit blocks in dom order for that
// TODO think about other expressions
//    * eq. `a && b => a, b`
// TODO and a more general "knowledge" system (ideally integrated into SCCP)
//    * make more complicated evals, eg. `a > b => a >= b`
fn cond_prop_func(prog: &mut Program, _: Function, use_info: &UseInfo, dom_info: &DomInfo) -> usize {
    // collect replacements
    let mut replacements = Replacements::default();

    for &block in dom_info.blocks() {
        if let &Terminator::Branch { cond, ref true_target, ref false_target } = &prog.get_block(block).terminator {
            let branch = Branch { block, true_block: true_target.block, false_block: false_target.block };

            // push immediate condition knowledge
            replacements.maybe_push_eq(prog, branch, true, cond, prog.const_bool(true).into());
            replacements.maybe_push_eq(prog, branch, false, cond, prog.const_bool(false).into());

            if let Some(cond) = cond.as_expr() {
                if let &ExpressionInfo::Comparison { kind, left, right } = prog.get_expr(cond) {
                    // push comparison knowledge
                    replacements.maybe_push_comparison(prog, branch, kind, left, right);
                }
            }
        }
    }

    // todo for a certain block, find the set of simplest replacements that apply
    // TODO remove these prints
    if !replacements.replacements.is_empty() {
        println!("Replacements:");
        for r in &replacements.replacements {
            println!("  {:?}", r);
        }
    }

    // apply replacements
    let mut replaced = 0;

    for replacement in replacements.replacements {
        // TODO only apply replacement if it's the simplest one that applies

        replaced += use_info.replace_value_usages_if(prog, replacement.complex, replacement.simple, |_, usage| {
            match usage {
                Usage::RootFunction(_) => false,
                // TODO support replacing  expression operands
                Usage::ExprOperand { .. } => false,

                Usage::InstrOperand { pos, usage: _ } =>
                    replacement.cond.applies_to_instr_in(dom_info, pos.block),

                Usage::TermOperand { pos, usage } => {
                    match usage {
                        TermOperand::BranchCond | TermOperand::ReturnValue =>
                            replacement.cond.applies_to_instr_in(dom_info, pos.block),
                        TermOperand::TargetArg { kind, index: _ } => {
                            match kind {
                                TargetKind::Jump =>
                                    replacement.cond.applies_to_instr_in(dom_info, pos.block),
                                TargetKind::BranchTrue =>
                                    replacement.cond.applies_to_target_in_branch(pos.block, true),
                                TargetKind::BranchFalse =>
                                    replacement.cond.applies_to_target_in_branch(pos.block, false),
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
        Value::Global(Global::GlobalSlot(_)) => 2,
        // TODO mark func params as more expensive than block params?
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