use win32;

fn exit(exitCode: u32) {
    win32::_ExitProcess@4(exitCode);
}
