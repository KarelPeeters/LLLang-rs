const STD_INPUT_HANDLE_NEG: int = 10;
const STD_OUTPUT_HANDLE_NEG: int = 11;
const STD_ERROR_HANDLE_NEG: int = 12;

const GENERIC_READ_HALF: int = 1073741824; //0x80000000 / 2
const FILE_APPEND_DATA: int = 4; //0x0004
const OPEN_ALWAYS: int = 4; //4
const FILE_ATTRIBUTE_NORMAL: int = 128; //0x00000080

extern fun _GetStdHandle@4(nStdHandle: int) -> int;

extern fun _CreateFileA@28(
    lpFileName: &byte,
    dwDesiredAccess: int,
    dwShareMode: int,
    lpSecurityAttributes: &void,
    dwCreationDisposition: int,
    dwFlagsAndAttributes: int,
    hTemplateFile: &void,
) -> int;

extern fun _WriteFile@20(
    hFile: int,
    lpBuffer: &byte,
    nNumberOfBytesToWrite: int,
    lpNumberOfBytesWritten: &int,
    lpOverlapped: &void,
) -> bool;