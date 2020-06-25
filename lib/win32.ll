//process
extern fun _ExitProcess@4(exitCode: int);

//console, io
extern fun _GetStdHandle@4(nStdHandle: int) -> int;
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
