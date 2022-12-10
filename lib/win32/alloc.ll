extern fun _GetProcessHeap@0() -> &void;
extern fun _HeapAlloc@12(hHeap: &void, dwFlags: int, dwBytes: int) -> &void;
extern fun _HeapFree@12(hHeap: &void, dwFlags: int, lpMem: &void) -> bool;
