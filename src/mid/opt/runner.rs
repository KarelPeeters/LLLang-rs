use std::collections::HashMap;
use std::ffi::OsStr;
use std::fmt::Debug;
use std::io;
use std::path::{Path, PathBuf};
use std::rc::Rc;

use crate::mid::analyse::dom_info::DomInfo;
use crate::mid::analyse::use_info::UseInfo;
use crate::mid::ir::{Function, Program};
use crate::mid::opt::DEFAULT_PASSES;
use crate::mid::opt::gc::gc;
use crate::mid::util::verify::verify;
use crate::tools::render_ir_as_svg;

// TODO add FunctionPass that only runs on changed functions
// TODO store which pass last changed the program/function and skip it if repeated and idempotent
pub trait ProgramPass: Debug {
    fn run(&self, prog: &mut Program, ctx: &mut PassContext) -> PassResult;

    // TODO create some common infrastructure for passes that are forced
    // idempotent by repeating until unchanged internally
    fn is_idempotent(&self) -> bool;
}

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub struct PassResult {
    pub changed: bool,
    // TODO change the meaning of these to be implicitly false if !changed
    pub preserved_dom_info: bool,
    pub preserved_use_info: bool,
}

#[derive(Debug, Copy, Clone)]
pub struct RunnerChecks {
    pub verify: bool,
    pub check_info_preserved: bool,
    pub check_changed: bool,
    pub check_idempotent: bool,
}

#[derive(Debug, Clone)]
pub struct RunnerSettings {
    pub max_loops: Option<u32>,
    pub checks: RunnerChecks,
    pub log_path_ir: Option<PathBuf>,
    pub log_path_svg: Option<PathBuf>,
}

pub struct PassRunner<'p> {
    settings: RunnerSettings,
    passes: Vec<&'p dyn ProgramPass>,
}

#[derive(Default)]
pub struct PassContext {
    use_info: Option<Rc<UseInfo>>,
    // TODO allow only invalidating a single function, ideally both in ProgramPass and FunctionPass?
    dom_info: HashMap<Function, Rc<DomInfo>>,
}

impl PassResult {
    pub fn safe(changed: bool) -> Self {
        Self {
            changed,
            preserved_dom_info: !changed,
            preserved_use_info: !changed,
        }
    }
}

impl<'p> PassRunner<'p> {
    pub fn new(settings: RunnerSettings, passes: impl IntoIterator<Item=&'p dyn ProgramPass>) -> Self {
        let passes = passes.into_iter().collect();
        Self { settings, passes }
    }

    pub fn with_default_passes(settings: RunnerSettings) -> Self {
        PassRunner::new(settings, DEFAULT_PASSES.iter().copied())
    }

    pub fn run(&self, prog: &mut Program) -> io::Result<()> {
        // clear logging paths
        if let Some(log_path_ir) = &self.settings.log_path_ir {
            clear_log_dir(log_path_ir, &["ir"])?;
        }
        if let Some(log_path_svg) = &self.settings.log_path_svg {
            clear_log_dir(log_path_svg, &["svg", "gv"])?;
        }

        let mut ctx = PassContext::default();
        let mut pass_index = 0;
        let mut loop_count = 0;

        // GC once at the start
        gc(prog);

        loop {
            if self.settings.max_loops.map_or(false, |max_loops| loop_count >= max_loops) {
                break;
            }
            loop_count += 1;

            let mut changed = false;

            for &pass in &self.passes {
                let pass_changed = self.run_pass_checked(prog, &mut ctx, pass, pass_index)?;

                changed |= pass_changed;
                pass_index += 1;

                // GC after every pass
                if pass_changed {
                    gc(prog);
                }
            }

            if !changed { break; }
        }

        Ok(())
    }

    fn run_pass_unchecked(&self, prog: &mut Program, ctx: &mut PassContext, pass: &dyn ProgramPass) -> io::Result<bool> {
        let result = pass.run(prog, ctx);

        if !result.changed {
            assert!(
                result.preserved_use_info && result.preserved_dom_info,
                "Pass {:?} didn't change the program but did not preserve use/dom info",
                pass
            );
        }

        ctx.apply_invalidation(result);

        Ok(result.changed)
    }

    fn run_pass_checked(&self, prog: &mut Program, ctx: &mut PassContext, pass: &dyn ProgramPass, i: u64) -> io::Result<bool> {
        let pass_name = format!("{:?}", pass);

        let settings = &self.settings;
        let checks = settings.checks;
        let needs_str = checks.check_changed || settings.log_path_ir.is_some();

        let str_before = if needs_str {
            Some(prog.to_string())
        } else {
            None
        };

        if let Some(log_path_ir) = &settings.log_path_ir {
            std::fs::write(log_path_ir.join(format!("{i}_{pass_name}_0_before.ir")), str_before.as_ref().unwrap())?;
        }
        if let Some(log_path_svg) = &settings.log_path_svg {
            render_ir_as_svg(prog, log_path_svg.join(format!("{i}_{pass_name}_0_before.svg")))?;
        }

        let changed = self.run_pass_unchecked(prog, ctx, pass)?;

        let str_after = if needs_str {
            Some(prog.to_string())
        } else {
            None
        };

        let str_changed = checks.check_changed && (str_before.as_ref().unwrap() != str_after.as_ref().unwrap());

        if changed || str_changed {
            if let Some(log_path_ir) = &settings.log_path_ir {
                std::fs::write(log_path_ir.join(format!("{i}_{pass_name}_1_after.ir")), str_after.as_ref().unwrap())?;
            }
            if let Some(log_path_svg) = &settings.log_path_svg {
                render_ir_as_svg(prog, log_path_svg.join(format!("{i}_{pass_name}_1_after.svg")))?;
            }
        }

        if checks.verify {
            verify(prog).unwrap();
        }

        if checks.check_changed {
            assert_eq!(str_changed, changed, "Changed flag mismatch for pass {}", pass_name);
        }

        if checks.check_info_preserved {
            ctx.assert_valid(prog);
        }

        if checks.check_idempotent && changed {
            let new_result = pass.run(prog, ctx);
            assert!(!new_result.changed, "Idempotency violation for pass {}", pass_name);
        }

        Ok(changed)
    }
}

impl PassContext {
    // TODO these are kind of sketchy, you need to call them before modifying prog/func
    //  ideally there would be a way to invalidate these things during the pass
    pub fn use_info(&mut self, prog: &Program) -> Rc<UseInfo> {
        self.use_info.get_or_insert_with(|| {
            Rc::new(UseInfo::new(prog))
        }).clone()
    }

    pub fn dom_info(&mut self, prog: &Program, func: Function) -> Rc<DomInfo> {
        self.dom_info.entry(func).or_insert_with(|| {
            Rc::new(DomInfo::new(prog, func))
        }).clone()
    }

    pub fn apply_invalidation(&mut self, result: PassResult) {
        let PassResult { changed: _, preserved_dom_info, preserved_use_info } = result;

        if !preserved_use_info {
            self.use_info = None;
        }
        if !preserved_dom_info {
            self.dom_info.clear();
        }
    }

    fn assert_valid(&self, prog: &Program) {
        if let Some(use_info) = &self.use_info {
            let expected = UseInfo::new(prog);
            assert_eq!(use_info.as_ref(), &expected);
        }

        for (&func, dom_info) in &self.dom_info {
            let expected = DomInfo::new(prog, func);
            assert_eq!(dom_info.as_ref(), &expected);
        }
    }
}

impl RunnerChecks {
    pub fn all() -> Self {
        Self {
            check_changed: true,
            check_info_preserved: true,
            check_idempotent: true,
            verify: true,
        }
    }

    pub fn none() -> Self {
        Self {
            check_changed: false,
            check_info_preserved: false,
            check_idempotent: false,
            verify: false,
        }
    }
}

fn clear_log_dir(dir: &Path, allowed_extensions: &[&str]) -> io::Result<()> {
    if dir.exists() {
        // ensure there are only expected files in the directory
        for entry in std::fs::read_dir(dir)? {
            let entry = entry?;

            assert!(entry.file_type()?.is_file(), "Found non-file in log dir {:?}", dir);

            let file_name = entry.file_name();
            let ext = Path::new(&file_name).extension();
            assert!(
                ext.map_or(false, |ext| allowed_extensions.iter().any(|allowed| OsStr::new(allowed) == ext)),
                "Found unexpected extension in log dir {:?}: {:?}",
                dir, file_name,
            );
        }

        // clear and recreate
        std::fs::remove_dir_all(dir)?;
    }
    std::fs::create_dir_all(dir)?;

    Ok(())
}