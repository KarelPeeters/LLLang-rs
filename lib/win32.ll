//process
extern fun _ExitProcess@4(exitCode: int);

//io
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
