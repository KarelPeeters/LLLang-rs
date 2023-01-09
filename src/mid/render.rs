use std::fmt::Write as _;
use std::io::Write;
use std::marker::PhantomData;

use indexmap::{IndexMap, IndexSet};
use itertools::Itertools;

use crate::mid::analyse::usage::{try_for_each_expr_tree_operand, try_for_each_usage_in_expr};
use crate::mid::analyse::use_info::UseInfo;
use crate::mid::ir::{Block, Expression, Function, Global, Immediate, Instruction, InstructionInfo, Program, Scoped, Value};
use crate::util::{Never, NeverExt};
use crate::util::arena::IndexType;

type Result = std::io::Result<()>;

pub fn render(prog: &Program, mut f: impl Write) -> Result {
    Renderer::new(prog).render(&mut f)
}

struct Renderer<'a, W: Write> {
    prog: &'a Program,
    func_expressions: IndexMap<Function, IndexSet<Expression>>,
    other_expressions: IndexSet<Expression>,

    // this is a hack so we don't have to repeat the W bound in every member function
    ph: PhantomData<W>,
}

impl<'a, W: Write> Renderer<'a, W> {
    pub fn new(prog: &'a Program) -> Self {
        let use_info = UseInfo::new(prog);

        let mut func_expressions: IndexMap<Function, IndexSet<Expression>> = IndexMap::new();
        let mut other_expressions: IndexSet<Expression> = use_info.values().filter_map(|v| v.as_expr()).collect();

        for value in use_info.values() {
            if let Value::Expr(expr) = value {
                for usage in &use_info[value] {
                    if let Some(func) = usage.as_dom_pos().ok().and_then(|pos| pos.function()) {
                        let set = func_expressions.entry(func).or_default();
                        set.insert(expr);
                        other_expressions.remove(&expr);
                        try_for_each_expr_tree_operand(prog, expr, |value, _, _| {
                            if let Value::Expr(value) = value {
                                set.insert(value);
                                other_expressions.remove(&expr);
                            }
                            Never::UNIT
                        }).no_err();
                    }
                }
            }
        }

        Self { prog, func_expressions, other_expressions, ph: PhantomData }
    }

    fn render(&self, f: &mut W) -> Result {
        let prog = self.prog;

        writeln!(f, "digraph {{")?;
        writeln!(f)?;

        for func in prog.nodes.funcs.keys() {
            self.render_func(f, func)?;
        }

        // render expressions that aren't used in any function
        for &expr in &self.other_expressions {
            self.render_expr(f, expr)?;
        }

        writeln!(f)?;
        writeln!(f, "}}")?;
        Ok(())
    }

    fn render_func(&self, f: &mut W, func: Function) -> Result {
        let prog = self.prog;
        let func_info = prog.get_func(func);

        writeln!(f, "subgraph cluster_func_{} {{", func.index())?;

        // TODO func name
        // TODO func signature
        // TODO func slots

        prog.try_visit_blocks(func_info.entry, |block| {
            self.render_block(f, block)
        })?;

        // render expressions used in this function
        for &expr in self.func_expressions.get(&func).unwrap_or(&IndexSet::new()) {
            self.render_expr(f, expr)?;
        }

        writeln!(f, "}}")?;
        Ok(())
    }

    fn render_block(&self, f: &mut W, block: Block) -> Result {
        let prog = self.prog;
        let block_info = prog.get_block(block);

        let mut rows = String::new();
        write!(&mut rows, "<tr><td align=\"center\" colspan=\"3\">block_{}</td></tr>", block.index()).unwrap();

        // TODO block params as first table row

        for &instr in &block_info.instructions {
            let ty = prog.type_of_value(instr.into());
            let ty_str = if ty == prog.ty_void() { "".to_owned() } else { prog.format_type(ty).to_string() };

            write!(
                &mut rows,
                "<tr><td port=\"instr_{}\" align=\"left\">instr_{}</td><td align=\"left\">{}</td><td align=\"left\">{}</td></tr>",
                instr.index(), instr.index(), quote_html(&ty_str), quote_html(&self.instr_to_str(instr))
            ).unwrap();
        }

        // TODO term kind and value
        // TODO targets with edge colors: blue jump, green true branch, red false branch
        // TODO target args as last table row

        write!(&mut rows, "<tr><td>term</td></tr>").unwrap();
        let label = format!("<<table border=\"0\">{}</table>>", rows);

        writeln!(f, "block_{} [label={}, shape=\"box\"];", block.index(), label)?;

        block_info.terminator.try_for_each_target(|target| {
            writeln!(f, "block_{} -> block_{};", block.index(), target.block.index())
        })?;

        Ok(())
    }

    fn render_expr(&self, f: &mut W, expr: Expression) -> Result {
        let prog = self.prog;
        let expr_info = prog.get_expr(expr);

        // let symbol = match expr_info {
        //     ExpressionInfo::Arithmetic { .. } => "arithmetic",
        //     ExpressionInfo::Comparison { .. } => "comparison",
        //     ExpressionInfo::TupleFieldPtr { .. } => "tuplefieldptr",
        //     ExpressionInfo::PointerOffSet { .. } => "pointeroffset",
        //     ExpressionInfo::Cast { .. } => "cast",
        // };

        writeln!(f, "expr_{} [label=expr_{}];", expr.index(), expr.index())?;

        try_for_each_usage_in_expr(expr_info, |value, _| {
            Self::write_edge(f, Some(format!("expr_{}", expr.index())), self.value_to_node(value))
        })?;

        Ok(())
    }

    fn instr_to_str(&self, instr: Instruction) -> String {
        let prog = self.prog;
        match *prog.get_instr(instr) {
            InstructionInfo::Load { addr, ty } =>
                format!("load {} [{}]", prog.format_type(ty), self.value_to_str(addr)),
            InstructionInfo::Store { addr, ty, value } =>
                format!("store {} [{}] <- {}", prog.format_type(ty), self.value_to_str(addr), self.value_to_str(value)),
            InstructionInfo::Call { target, ref args } => {
                let args = args.iter().map(|&arg| self.value_to_str(arg)).join(", ");
                format!("call {} ( {} )", self.value_to_str(target), args)
            }
            InstructionInfo::BlackBox { value } =>
                format!("blackbox {}", self.value_to_str(value)),
        }
    }

    fn value_to_node(&self, value: Value) -> Option<String> {
        match value {
            Value::Immediate(_) => None,
            Value::Global(_) => None,
            Value::Scoped(value) => match value {
                Scoped::Slot(_) => None,
                Scoped::Param(_) => None,
                Scoped::Instr(_) => None,
            }
            Value::Expr(expr) => {
                Some(format!("expr_{}", expr.index()))
            }
        }
    }

    fn value_to_str(&self, value: Value) -> String {
        match value {
            Value::Immediate(value) => match value {
                Immediate::Void => "void".to_owned(),
                Immediate::Undef(_) => "undef".to_owned(),
                Immediate::Const(cst) => format!("const({})", cst.value.display_value()),
            }
            Value::Global(value) => match value {
                Global::Func(func) => format!("func_{}", func.index()),
                Global::Extern(ext) => format!("ext_{}", ext.index()),
                Global::Data(data) => format!("data_{}", data.index()),
            }
            Value::Scoped(value) => match value {
                Scoped::Slot(slot) => format!("slot_{}", slot.index()),
                Scoped::Param(param) => format!("param_{}", param.index()),
                Scoped::Instr(instr) => format!("instr_{}", instr.index()),
            }
            Value::Expr(expr) => format!("expr_{}", expr.index()),
        }
    }

    fn write_edge(f: &mut W, from: Option<String>, to: Option<String>) -> Result {
        if let (Some(from), Some(to)) = (from, to) {
            writeln!(f, "{} -> {};", from, to)
        } else {
            Ok(())
        }
    }
}

fn quote_html(s: &str) -> String {
    s.replace('&', "&amp;").replace('<', "&lt;").replace('>', "&gt;")
}