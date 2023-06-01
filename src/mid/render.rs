use std::fmt::Write as _;
use std::io::Write;
use std::marker::PhantomData;

use derive_more::From;
use indexmap::{IndexMap, IndexSet};
use itertools::Itertools;

use crate::mid::analyse::usage::TargetKind;
use crate::mid::analyse::use_info::UseInfo;
use crate::mid::ir::{Block, CastKind, Expression, ExpressionInfo, Function, Global, Immediate, Instruction, InstructionInfo, Program, Scoped, Signed, StackSlot, Target, Terminator, Value};
use crate::util::arena::IndexType;
use crate::util::internal_iter::InternalIterator;

type Result<T = ()> = std::result::Result<T, Error>;

// trick to avoid having to unwrap every fmt error when writing to string
#[derive(From)]
enum Error {
    IO(std::io::Error),
    Fmt(std::fmt::Error),
}

// TODO rename to include what format we are writing?
pub fn render(prog: &Program, mut f: impl Write) -> std::io::Result<()> {
    let result = Renderer::new(prog).render(&mut f);

    match result {
        Ok(()) => Ok(()),
        Err(Error::IO(e)) => Err(e),
        Err(Error::Fmt(_)) => unreachable!(),
    }
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

        let mut mark_expr = |func, expr| {
            let set = func_expressions.entry(func).or_default();
            set.insert(expr);
            other_expressions.remove(&expr);
        };

        for value in use_info.values() {
            if let Value::Expr(expr) = value {
                for usage in &use_info[value] {
                    if let Some(func) = usage.as_dom_pos().ok().and_then(|pos| pos.function()) {
                        mark_expr(func, expr);

                        prog.expr_tree_iter(expr).try_for_each(|(value, _, _)| {
                            if let Value::Expr(value) = value {
                                mark_expr(func, value);
                            }
                        });
                    }
                }
            }
        }

        Self { prog, func_expressions, other_expressions, ph: PhantomData }
    }

    fn render(&self, f: &mut W) -> Result {
        let prog = self.prog;

        writeln!(f, "digraph {{")?;

        writeln!(f, r#"fontname="Arial,sans-serif""#)?;
        writeln!(f, r#"node [fontname="Arial,sans-serif"]"#)?;
        writeln!(f, r#"edge [fontname="Arial,sans-serif"]"#)?;

        writeln!(f, "compound=true;")?;

        writeln!(f)?;

        for func in prog.nodes.funcs.keys() {
            self.render_func(f, func)?;
        }

        // render expressions that aren't used in any function
        self.render_expressions(f, "global", &self.other_expressions)?;

        self.render_data(f)?;

        // render root pointers
        for (i, (name, &func)) in prog.root_functions.iter().enumerate() {
            writeln!(f, r#"root_{} [label=<{:?}>, shape=diamond];"#, i, name)?;
            writeln!(f, r#"root_{} -> func_{}_entry [lhead=cluster_func_{}];"#, i, func.index(), func.index())?;
        }

        writeln!(f)?;
        writeln!(f, "}}")?;
        Ok(())
    }

    fn render_data(&self, f: &mut W) -> Result {
        let prog = self.prog;
        if prog.nodes.datas.len() == 0 {
            return Ok(());
        }

        let mut rows = String::new();
        let r = &mut rows;

        write!(r, r#"<tr><td colspan="3"><b>Data</b></td></tr>"#)?;

        for (data, data_info) in &prog.nodes.datas {
            let bytes = &data_info.bytes;
            let limit = 8;

            let bytes_str = if bytes.len() > limit {
                format!("{:?}", &bytes[..limit]).replace(']', ", ...]")
            } else {
                format!("{:?}", bytes)
            };

            write!(
                r,
                "<tr><td>data_{}</td><td>{}</td><td>{}</td></tr>",
                data.index(), quote_html(prog.format_type(data_info.ty).to_string()), bytes_str
            )?;
        }

        writeln!(f, r#"data [label=<<table border="0">{rows}</table>>, shape="box", style="rounded"]"#)?;
        Ok(())
    }

    fn render_func(&self, f: &mut W, func: Function) -> Result {
        let prog = self.prog;
        let func_info = prog.get_func(func);

        writeln!(f, "subgraph cluster_func_{} {{", func.index())?;

        let mut rows = String::new();
        let r = &mut rows;

        // header
        let name = if let Some(name) = &func_info.debug_name {
            format!("func_{} {:?}", func.index(), name)
        } else {
            format!("func_{}", func.index())
        };
        write!(r, "<tr><td><b>{}</b></td></tr>", name)?;
        write!(r, "<tr><td>{}</td></tr>", quote_html(prog.format_type(func_info.ty).to_string()))?;
        writeln!(f, r#"label = <<table border="0">{}</table>>;"#, rows)?;

        // slots
        self.render_slots(f, func, &func_info.slots)?;

        // blocks
        prog.reachable_blocks(func_info.entry).try_for_each(|block| {
            self.render_block(f, block)
        })?;

        // entry
        writeln!(f, r#"func_{}_entry [label="", shape=diamond];"#, func.index())?;
        writeln!(f, "func_{}_entry -> block_{};", func.index(), func_info.entry.index())?;

        // expressions
        if let Some(expressions) = self.func_expressions.get(&func) {
            self.render_expressions(f, &format!("func_{}", func.index()), expressions)?;
        }

        writeln!(f, "}}")?;
        Ok(())
    }

    fn render_slots(&self, f: &mut W, func: Function, slots: &[StackSlot]) -> Result {
        if slots.is_empty() {
            return Ok(());
        }

        let prog = self.prog;

        let mut rows = String::new();
        let r = &mut rows;

        for &slot in slots {
            let slot_info = prog.get_slot(slot);
            let ty = slot_info.inner_ty;
            let slot_name = slot_info.debug_name.as_ref().map_or("", |s| s);

            write!(
                r,
                "<tr><td>slot_{}</td><td>{}</td><td>{:?}</td></tr>",
                slot.index(), quote_html(prog.format_type(ty).to_string()), quote_html(slot_name),
            )?;
        }

        write!(
            f,
            r#"func_{}_slots [label=<<table border="0">{}</table>>, shape="box", style="rounded"]"#,
            func.index(), rows
        )?;
        Ok(())
    }

    fn render_block(&self, f: &mut W, block: Block) -> Result {
        let prog = self.prog;
        let block_info = prog.get_block(block);

        let rows = &mut String::new();

        let name = if let Some(name) = &block_info.debug_name {
            format!("block_{} {:?}", block.index(), name)
        } else {
            format!("block_{}", block.index())
        };
        write!(rows, r#"<tr><td align="center" colspan="3"><b>{}</b></td></tr>"#, name)?;

        for &param in &block_info.params {
            let ty = prog.type_of_value(param.into());
            write!(
                rows,
                r#"<tr><td align="left">param_{}</td><td align="left">{}</td></tr>"#,
                param.index(), quote_html(prog.format_type(ty).to_string()),
            )?;
        }

        for &instr in &block_info.instructions {
            let ty = prog.type_of_value(instr.into());
            let ty_str = if ty == prog.ty_void() { "".to_owned() } else { prog.format_type(ty).to_string() };

            write!(
                rows,
                r#"<tr><td align="left">instr_{}</td><td align="left">{}</td><td align="left">{}</td></tr>"#,
                instr.index(), quote_html(ty_str), quote_html(self.instr_to_str(instr))
            )?;
        }

        write!(rows, "{}", self.terminator_to_table_str(&block_info.terminator)?)?;

        let label = format!(r#"<<table border="0">{}</table>>"#, rows);
        writeln!(f, r#"block_{} [label={}, shape="box"];"#, block.index(), label)?;

        block_info.terminator.targets().try_for_each(|(target, kind)| {
            let color = match kind {
                TargetKind::Jump => "black",
                TargetKind::BranchTrue => "green",
                TargetKind::BranchFalse => "red",
            };

            let dir = if target.block == block {
                "back"
            } else {
                "forward"
            };

            writeln!(f, "block_{} -> block_{} [color={color}, dir={dir}];", block.index(), target.block.index())
        })?;

        Ok(())
    }

    fn terminator_to_table_str(&self, terminator: &Terminator) -> Result<String> {
        let mut result = String::new();
        let f = &mut result;
        match *terminator {
            Terminator::Jump { ref target } => {
                write!(f, r#"<tr><td colspan="2" align="left">jump</td><td align="left">{}</td></tr>"#, self.target_to_str(target))?;
            }
            Terminator::Branch { cond, ref true_target, ref false_target } => {
                write!(f, r#"<tr><td colspan="2" align="left">branch</td><td align="left">{}</td></tr>"#, self.value_to_str(cond))?;
                write!(f, r#"<tr><td></td><td></td><td align="left">{}</td></tr>"#, self.target_to_str(true_target))?;
                write!(f, r#"<tr><td></td><td></td><td align="left">{}</td></tr>"#, self.target_to_str(false_target))?;
            }
            Terminator::Return { value } => {
                write!(f, r#"<tr><td colspan="2" align="left">return</td><td align="left">{}</td></tr>"#, self.value_to_str(value))?;
            }
            Terminator::Unreachable => {
                write!(f, r#"<tr><td colspan="2" align="left">unreachable</td></tr>"#)?;
            }
            Terminator::LoopForever => {
                write!(f, r#"<tr><td colspan="2" align="left">loopforever</td></tr>"#)?;
            }
        }
        Ok(result)
    }

    fn target_to_str(&self, target: &Target) -> String {
        let args = target.args.iter().map(|&arg| self.value_to_str(arg)).join(", ");
        format!("block_{} ({})", target.block.index(), args)
    }

    fn render_expressions(&self, f: &mut W, prefix: &str, expressions: &IndexSet<Expression>) -> Result {
        if expressions.is_empty() {
            return Ok(());
        }

        let prog = self.prog;

        let mut rows = String::new();
        let r = &mut rows;

        for &expr in expressions {
            let expr_info = prog.get_expr(expr);

            let parts = self.expr_info_to_parts(expr_info)
                .iter()
                .map(|p| format!(r#"<td align="left">{}</td>"#, quote_html(p)))
                .join("");

            let index = expr.index();

            let ty = prog.type_of_value(expr.into());
            let ty_str = prog.format_type(ty).to_string();

            write!(
                r,
                r#"<tr><td align="left">expr_{index}</td><td align="left">{}</td>{}</tr>"#,
                quote_html(ty_str), parts,
            )?;
        }

        writeln!(f, r#"{}_expressions [label=<<table border="0">{}</table>> shape="box" style="rounded"];"#, prefix, &rows)?;

        Ok(())
    }

    fn instr_to_str(&self, instr: Instruction) -> String {
        let prog = self.prog;
        match *prog.get_instr(instr) {
            InstructionInfo::Load { addr, ty } =>
                format!("load {} [{}]", prog.format_type(ty), self.value_to_str(addr)),
            InstructionInfo::Store { addr, ty, value } =>
                format!("store {} [{}] <- {}", prog.format_type(ty), self.value_to_str(addr), self.value_to_str(value)),
            InstructionInfo::Call { target, ref args, conv } => {
                let args = args.iter().map(|&arg| self.value_to_str(arg)).join(", ");
                format!("call {:?} {} ( {} )", conv, self.value_to_str(target), args)
            }
            InstructionInfo::BlackBox { value } =>
                format!("blackbox {}", self.value_to_str(value)),
        }
    }

    fn expr_info_to_parts(&self, expr_info: &ExpressionInfo) -> Vec<String> {
        let prog = self.prog;

        let v = |value| self.value_to_str(value);
        let t = |ty| prog.format_type(ty).to_string();

        match *expr_info {
            ExpressionInfo::Arithmetic { kind, left, right } =>
                vec![shorten_signed(format!("{:?}", kind)), v(left), v(right)],
            ExpressionInfo::Comparison { kind, left, right } =>
                vec![shorten_signed(format!("{:?}", kind)), v(left), v(right)],
            ExpressionInfo::TupleFieldPtr { base, index, tuple_ty } =>
                vec![format!("TupleFieldPtr"), v(base), index.to_string(), t(tuple_ty)],
            ExpressionInfo::PointerOffSet { ty, base, index } =>
                vec![format!("PointerOffSet"), v(base), v(index), t(ty)],
            ExpressionInfo::Cast { ty: _, kind, value } =>
                vec![short_cast_kind(kind).to_string(), v(value)],
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
}

#[allow(dead_code)]
fn invis_node(f: &mut impl Write, name: impl AsRef<str>) -> Result {
    writeln!(f, "{} [style=invis];", name.as_ref())?;
    Ok(())
}

fn quote_html(s: impl AsRef<str>) -> String {
    s.as_ref().replace('&', "&amp;").replace('<', "&lt;").replace('>', "&gt;")
}

fn shorten_signed(s: impl AsRef<str>) -> String {
    s.as_ref().replace("Unsigned", "U").replace("Signed", "S")
}

fn short_cast_kind(kind: CastKind) -> &'static str {
    match kind {
        CastKind::IntTruncate => "Trunc",
        CastKind::IntExtend(Signed::Signed) => "Ext(S)",
        CastKind::IntExtend(Signed::Unsigned) => "Ext(U)",
    }
}