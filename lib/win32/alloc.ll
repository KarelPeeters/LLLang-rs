extern fn _GetProcessHeap@0() -> &void;
extern fn _HeapAlloc@12(hHeap: &void, dwFlags: int, dwBytes: int) -> &void;
extern fn _HeapFree@12(hHeap: &void, dwFlags: int, lpMem: &void) -> bool;
