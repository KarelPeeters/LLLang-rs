use std::fs::File;
use std::path::Path;
use std::process::{Command, ExitStatus};

use crate::mid;
use crate::mid::render::render;

// TODO use env vars or auto discovery for these tools
// TODO get these to work on linux
pub fn run_nasm(path_asm_in: &Path, path_obj_out: &Path) -> std::io::Result<ExitStatus> {
    assert!(path_asm_in.extension().unwrap().to_str().unwrap() == "asm");
    assert!(path_obj_out.extension().unwrap().to_str().unwrap() == "obj");

    Command::new("nasm")
        .arg("-O0")
        .arg("-fwin64")
        .arg("-g")
        .arg("-o")
        .arg(path_obj_out)
        .arg(path_asm_in)
        .status()
}

pub fn run_link(path_obj_in: &Path, path_exe_out: &Path) -> std::io::Result<ExitStatus> {
    assert!(path_obj_in.extension().unwrap().to_str().unwrap() == "obj");
    assert!(path_exe_out.extension().unwrap().to_str().unwrap() == "exe");

    Command::new(r#"C:\Program Files\Microsoft Visual Studio\2022\Community\VC\Tools\MSVC\14.36.32532\bin\Hostx64\x64\link.exe"#)
        .arg("/nologo")
        .arg("/debug")
        .arg("/subsystem:console")
        .arg("/nodefaultlib")
        .arg("/entry:main")
        .arg(format!("/out:{}", path_exe_out.to_str().unwrap()))
        .arg(path_obj_in)
        .arg(r#"C:\Program Files (x86)\Windows Kits\10\Lib\10.0.22000.0\um\x64\kernel32.lib"#)
        .status()
}

pub fn render_ir_as_svg(prog: &mid::ir::Program, path: impl AsRef<Path>) -> std::io::Result<()> {
    let path = path.as_ref();

    let path_gv = path.with_extension("gv");
    let mut render_writer = File::create(&path_gv)?;
    render(prog, &mut render_writer)?;

    let dot_output = Command::new("dot").arg(&path_gv).arg("-Tsvg").output()?;
    eprintln!("{}", std::str::from_utf8(&dot_output.stderr).unwrap());
    let path_svg = path.with_extension("svg");
    std::fs::write(path_svg, dot_output.stdout)?;

    std::fs::remove_file(path_gv)?;

    Ok(())
}