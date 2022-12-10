use win32::alloc;

fun malloc(size: int) -> &void {
    let heap = alloc::_GetProcessHeap@0();
    return alloc::_HeapAlloc@12(heap, 0, size);
}

fun free(mem: &void) -> bool {
    let heap = alloc::_GetProcessHeap@0();
    return alloc::_HeapFree@12(heap, 0, mem);
}

/// overlapping memory is undefined behavior
fun memcpy(dest: &byte, src: &byte, len: int) {
    for i in 0..len {
        *(dest + i) = *(src + i);
    }
}