use std::path::Path;
use std::process::{Command, ExitStatus};

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

    Command::new(r#"C:\Program Files (x86)\Microsoft Visual Studio\2019\Community\VC\Tools\MSVC\14.29.30133\bin\Hostx64\x64\link.exe"#)
        .arg("/nologo")
        .arg("/debug")
        .arg("/subsystem:console")
        .arg("/nodefaultlib")
        .arg("/entry:main")
        .arg(format!("/out:{}", path_exe_out.to_str().unwrap()))
        .arg(path_obj_in)
        .arg(r#"C:\Program Files (x86)\Windows Kits\10\Lib\10.0.19041.0\um\x64\kernel32.lib"#)
        .status()
}