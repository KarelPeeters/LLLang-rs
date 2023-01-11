// TODO switch to generating all of this from the header files directly
//   hopefully the compiler is fast enough to deal with the thousands of items that will yield :)

// minwindef.h
type BYTE = u8;
type SHORT = i16;
type USHORT = u16;
// bool, int, long, dword are all 32-bit
type BOOL = i32;
type DWORD = u32;
type INT = i32;
type UINT = u32;
type LONG = i32;
type ULONG = u32;
// only "long long" is 64-bit
type LONGLONG = i64;
type ULONGLONG = u64;

type SIZE_T = usize;
type HANDLE = &void;

type LPVOID = &void;
type LPCVOID = &void;
type LPCSTR = &i8; // pointer to zero-terminated string
type LPDWORD = &u32;

// heapapi.h
extern fn _GetProcessHeap@0() -> HANDLE;

extern fn _HeapAlloc@12(
    hHeap: HANDLE,
    dwFlags: DWORD,
    dwBytes: SIZE_T
) -> LPVOID;

extern fn _HeapFree@12(
    hHeap: HANDLE,
    dwFlags: DWORD,
    lpMem: LPVOID
) -> BOOL;

// processenv.h
const STD_INPUT_HANDLE: DWORD = 0xfffffff6; // -10
const STD_OUTPUT_HANDLE: DWORD = 0xfffffff5; // -11
const STD_ERROR_HANDLE: DWORD = 0xfffffff4; // -12

const FILE_GENERIC_READ: DWORD = 0x120089;
const FILE_GENERIC_WRITE: DWORD = 0x120116;
const FILE_GENERIC_EXECUTE: DWORD = 0x1200a0;

const CREATE_NEW: DWORD = 1;
const CREATE_ALWAYS: DWORD = 2;
const OPEN_EXISTING: DWORD = 3;
const OPEN_ALWAYS: DWORD = 4;
const TRUNCATE_EXISTING: DWORD = 5;

const FILE_ATTRIBUTE_NORMAL: DWORD = 0x80;

extern fn _GetStdHandle@4(
    nStdHandle: DWORD
) -> HANDLE;

extern fn _CreateFileA@28(
    lpFileName: LPCSTR,
    dwDesiredAccess: DWORD,
    dwShareMode: DWORD,
    lpSecurityAttributes: &void, // TODO define the proper struct for this
    dwCreationDisposition: DWORD,
    dwFlagsAndAttributes: DWORD,
    hTemplateFile: HANDLE,
) -> HANDLE;

extern fn _WriteFile@20(
    hFile: HANDLE,
    lpBuffer: LPCVOID,
    nNumberOfBytesToWrite: DWORD,
    lpNumberOfBytesWritten: LPDWORD,
    lpOverlapped: &void, // TODO define the proper struct for this
) -> BOOL;

// processthreadsapi.h
const CREATE_SUSPENDED: DWORD = 0x00000004;

extern fn _ExitProcess@4(exitCode: UINT);

extern fn _CreateThread@24(
  lpThreadAttributes: &void, // TODO define the proper struct for this
  dwStackSize: SIZE_T,
  lpStartAddress: (LPVOID) -> DWORD,
  lpParameter: LPVOID, // optional
  dwCreationFlags: DWORD,
  lpThreadI: LPDWORD, // optional
) -> HANDLE;

// synchapi.h
extern fn _WaitForSingleObject@8(
  hHandle: HANDLE,
  dwMilliseconds: DWORD,
) -> DWORD;

extern fn _WaitForMultipleObjects@16(
  nCount: DWORD,
  lpHandles: &HANDLE,
  bWaitAll: BOOL,
  dwMilliseconds: DWORD,
) -> DWORD;

// sysinfoapi.h
extern fn _GetPhysicallyInstalledSystemMemory@4(
    TotalMemoryInKilobytes: &ULONGLONG,
) -> BOOL;
