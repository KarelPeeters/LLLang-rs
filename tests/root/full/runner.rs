use std::path::Path;
use std::process::Command;
use std::str::FromStr;

use lllang::back;
use lllang::front::pos::{FileId, Pos, Span};
use lllang::mid::opt::runner::{PassRunner, RunnerChecks, RunnerSettings};
use lllang::mid::util::verify::verify;
use lllang::tools::{run_link, run_nasm};

use crate::root::util::parse_ir_standalone;

// TODO fuzz different optimization passes
pub fn run_cases(src: &str) {
    std::fs::create_dir_all("ignored/tmp").unwrap();
    let tmp_folder = tempfile::tempdir_in("ignored/tmp").unwrap();
    println!("Using temp dir: {:?}", tmp_folder);

    let cases = collect_cases(src);
    let settings = RunnerSettings {
        max_loops: None,
        checks: RunnerChecks::all(),
        log_path_ir: None,
        log_path_svg: None,
    };
    let runner = PassRunner::with_default_passes(settings);

    for case in cases {
        run_case(&runner, tmp_folder.path(), &case);
    }
}

fn run_case(runner: &PassRunner, tmp_folder: &Path, case: &TestCase) {
    println!("{:?}", case);

    let mut prog = parse_ir_standalone(&case.code);
    verify(&prog).unwrap();

    for &opt in case.instr.opt_values() {
        println!("Optimizing: {}", opt);
        if opt {
            runner.run(&mut prog).unwrap();
            verify(&prog).unwrap();
        }

        let asm_path = tmp_folder.join("tmp.asm");
        let obj_path = tmp_folder.join("tmp.obj");
        let exe_path = tmp_folder.join("tmp.exe");

        println!("Lowering");
        let asm = back::x86_asm_select::lower_new(&mut prog);
        std::fs::write(&asm_path, &asm).unwrap();
        println!("Assembling");
        assert!(run_nasm(&asm_path, &obj_path).unwrap().success());
        println!("Linking");
        assert!(run_link(&obj_path, &exe_path).unwrap().success());

        println!("Running");
        let result = Command::new(exe_path).status().unwrap().code().unwrap() as u32;
        assert_eq!(case.instr.exit_code, result, "Wrong exit code");
    }
}

fn collect_cases(src: &str) -> Vec<TestCase> {
    let mut cases = vec![];

    let mut curr_instr = None;
    let mut curr_code = String::new();

    let mut start_line_index = 0;
    let mut last_non_empty_line_index = 0;

    for (line_zero_index, line) in src.lines().enumerate() {
        let line_index = line_zero_index + 1;

        if let Some(rest) = line.strip_prefix("// TEST: ") {
            let new_instr = TestInstruction::from_str(rest)
                .unwrap_or_else(|_| panic!("Invalid test instruction on line {}", line_index));

            if let Some(old_instr) = curr_instr {
                assert!(!curr_code.trim().is_empty(), "Empty test case before line {}", line_index);
                cases.push(TestCase {
                    instr: old_instr,
                    code: curr_code,
                    span: Span::new(pos(start_line_index), pos(last_non_empty_line_index)),
                });
            } else {
                assert!(curr_code.trim().is_empty(), "Orphan code before line {}", line_index);
            }

            start_line_index = line_index;
            curr_instr = Some(new_instr);
            curr_code = String::new();
        } else {
            curr_code.push_str(line);
            curr_code.push('\n');
        }

        if !line.is_empty() {
            last_non_empty_line_index = line_index;
        }
    }

    if let Some(old_instr) = curr_instr {
        assert!(!curr_code.trim().is_empty(), "Empty test case before line {}", last_non_empty_line_index);
        cases.push(TestCase {
            instr: old_instr,
            code: curr_code,
            span: Span::new(pos(start_line_index), pos(last_non_empty_line_index)),
        });
    } else {
        assert!(curr_code.trim().is_empty(), "Orphan code before line {}", last_non_empty_line_index);
    }

    cases
}

fn pos(line: usize) -> Pos {
    Pos {
        file: FileId(0),
        line,
        col: 0,
    }
}

#[derive(Debug, Clone)]
struct TestCase {
    #[allow(dead_code)]
    span: Span,
    instr: TestInstruction,
    code: String,
}

#[derive(Debug, Copy, Clone)]
struct TestInstruction {
    opt: Option<bool>,
    exit_code: u32,
}

impl TestInstruction {
    fn opt_values(self) -> &'static [bool] {
        match self.opt {
            Some(true) => &[true],
            Some(false) => &[false],
            None => &[true, false],
        }
    }
}

#[derive(Debug, Clone)]
struct InvalidTestInstruction(String);

impl FromStr for TestInstruction {
    type Err = InvalidTestInstruction;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let (rem, opt) = if let Some(rem) = s.strip_prefix("opt, ") {
            (rem, Some(true))
        } else if let Some(rem) = s.strip_prefix("no-opt, ") {
            (rem, Some(false))
        } else {
            (s, None)
        };

        if let Some(code) = rem.strip_prefix("exit ") {
            let exit_code = code.parse::<u32>().map_err(|_| InvalidTestInstruction(rem.to_string()))?;
            return Ok(TestInstruction {
                opt,
                exit_code,
            });
        }

        Err(InvalidTestInstruction(rem.to_string()))
    }
}
