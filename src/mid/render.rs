use std::fmt::Write as _;
use std::io::Write;
use std::marker::PhantomData;

use indexmap::{IndexMap, IndexSet};
use itertools::Itertools;

use crate::mid::analyse::usage::{try_for_each_expr_tree_operand, try_for_each_usage_in_expr};
use crate::mid::analyse::use_info::UseInfo;
use crate::mid::ir::{Block, Expression, ExpressionInfo, Function, Global, Immediate, Instruction, InstructionInfo, Program, Scoped, Target, Terminator, Value};
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
        self.render_expressions(f, "global", &self.other_expressions)?;

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
        if let Some(expressions) = self.func_expressions.get(&func) {
            self.render_expressions(f, &format!("func_{}", func.index()), expressions)?;
        }

        writeln!(f, "}}")?;
        Ok(())
    }

    fn render_block(&self, f: &mut W, block: Block) -> Result {
        let prog = self.prog;
        let block_info = prog.get_block(block);

        let rows = &mut String::new();
        write!(rows, "<tr><td align=\"center\" colspan=\"3\">block_{}</td></tr>", block.index()).unwrap();

        // TODO block params as first table row

        for &instr in &block_info.instructions {
            let ty = prog.type_of_value(instr.into());
            let ty_str = if ty == prog.ty_void() { "".to_owned() } else { prog.format_type(ty).to_string() };

            write!(
                rows,
                "<tr><td port=\"instr_{}\" align=\"left\">instr_{}</td><td align=\"left\">{}</td><td align=\"left\">{}</td></tr>",
                instr.index(), instr.index(), quote_html(&ty_str), quote_html(&self.instr_to_str(instr))
            ).unwrap();
        }

        write!(rows, "{}", self.terminator_to_table_str(&block_info.terminator)).unwrap();

        let label = format!("<<table border=\"0\">{}</table>>", rows);
        writeln!(f, "block_{} [label={}, shape=\"box\"];", block.index(), label)?;

        // TODO targets with edge colors: blue jump, green true branch, red false branch
        block_info.terminator.try_for_each_target(|target| {
            writeln!(f, "block_{} -> block_{};", block.index(), target.block.index())
        })?;

        Ok(())
    }

    fn terminator_to_table_str(&self, terminator: &Terminator) -> String {
        let mut result = String::new();
        let f = &mut result;
        match *terminator {
            Terminator::Jump { ref target } => {
                write!(f, "<tr><td colspan=\"2\" align=\"left\">jump</td><td align=\"left\">{}</td></tr>", self.target_to_str(target)).unwrap();
            }
            Terminator::Branch { cond, ref true_target, ref false_target } => {
                write!(f, "<tr><td colspan=\"2\" align=\"left\">branch</td><td align=\"left\">{}</td></tr>", self.value_to_str(cond)).unwrap();
                write!(f, "<tr><td></td><td></td><td align=\"left\">{}</td></tr>", self.target_to_str(true_target)).unwrap();
                write!(f, "<tr><td></td><td></td><td align=\"left\">{}</td></tr>", self.target_to_str(false_target)).unwrap();
            }
            Terminator::Return { value } => {
                write!(f, "<tr><td colspan=\"2\" align=\"left\">return</td><td align=\"left\">{}</td></tr>", self.value_to_str(value)).unwrap();
            }
            Terminator::Unreachable => {
                write!(f, "<tr><td colspan=\"2\" align=\"left\">unreachable</td></tr>").unwrap();
            }
            Terminator::LoopForever => {
                write!(f, "<tr><td colspan=\"2\" align=\"left\">loopforever</td></tr>").unwrap();
            }
        }
        result
    }

    fn target_to_str(&self, target: &Target) -> String {
        let args = target.args.iter().map(|&arg| self.value_to_str(arg)).join(", ");
        format!("block_{} ({})", target.block.index(), args)
    }

    fn render_expressions(&self, f: &mut W, prefix: &str, expressions: &IndexSet<Expression>) -> Result {
        let prog = self.prog;

        let mut rows = String::new();
        let r = &mut rows;

        for &expr in expressions {
            let expr_info = prog.get_expr(expr);
            let expr_info_str = self.expr_info_to_str(expr_info);

            let ty = prog.type_of_value(expr.into());
            let ty_str = prog.format_type(ty).to_string();

            let index = expr.index();

            write!(
                r,
                "<tr>\
                <td align=\"left\" port=\"expr_{index}_def\">expr_{index}</td>\
                <td align=\"left\">{}</td>\
                <td align=\"left\" port=\"expr_{index}_use\">{}</td>\
                </tr>",
                quote_html(&ty_str), quote_html(&expr_info_str)
            ).unwrap();
        }

        writeln!(f, "{}_expressions [label=<<table border=\"0\">{}</table>> shape=\"box\" style=\"rounded\"];", prefix, &rows).unwrap();

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

    fn expr_info_to_str(&self, expr_info: &ExpressionInfo) -> String {
        let prog = self.prog;

        match *expr_info {
            ExpressionInfo::Arithmetic { kind, left, right } =>
                format!("{:?} {}, {}", kind, self.value_to_str(left), self.value_to_str(right)),
            ExpressionInfo::Comparison { kind, left, right } =>
                format!("{:?} {}, {}", kind, self.value_to_str(left), self.value_to_str(right)),
            ExpressionInfo::TupleFieldPtr { base, index, tuple_ty } =>
                format!("TupleFieldPtr {}, {}, {}", self.value_to_str(base), index, prog.format_type(tuple_ty)),
            ExpressionInfo::PointerOffSet { ty, base, index } =>
                format!("PointerOffSet {}, {}, {}", self.value_to_str(base), self.value_to_str(index), prog.format_type(ty)),
            ExpressionInfo::Cast { ty, kind, value } =>
                format!("Cast {} as {}, {:?}", self.value_to_str(value), self.prog.format_type(ty), kind),
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