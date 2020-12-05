//TODO should handles be int or &void?

//process
extern fun _ExitProcess@4(exitCode: int);

//io
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

//threads
extern fun _CreateThread@24(
  lpThreadAttributes: &void,
  dwStackSize: int,
  lpStartAddress: (&int) -> int,
  lpParameter: &int,
  dwCreationFlags: int,
  lpThreadI: &int,
) -> int;

//sync
extern fun _WaitForSingleObject@8(
  hHandle: int,
  dwMilliseconds: int,
) -> int;

extern fun _WaitForMultipleObjects@16(
  nCount: int,
  lpHandles: &int,
  bWaitAll: bool,
  dwMilliseconds: int,
) -> int;

//info
extern fun _GetPhysicallyInstalledSystemMemory@4(
  TotalMemoryInKilobytes: &int,
) -> bool;
