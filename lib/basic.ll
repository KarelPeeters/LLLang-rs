use win32;

fn exit(exitCode: int) {
    win32::processthread::_ExitProcess@4(exitCode);
}
