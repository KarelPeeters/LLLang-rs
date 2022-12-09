use win32;

fun exit(exitCode: int) {
    win32::processthread::_ExitProcess@4(exitCode);
}
