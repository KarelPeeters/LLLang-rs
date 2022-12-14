use win32;

fn malloc(size: u32) -> &void {
    let heap = win32::_GetProcessHeap@0();
    return win32::_HeapAlloc@12(heap, 0, size);
}

fn free(mem: &void) -> bool {
    let heap = win32::_GetProcessHeap@0();
    return win32::_HeapFree@12(heap, 0, mem) != 0;
}

/// overlapping memory is undefined behavior
fn memcpy(dest: &u8, src: &u8, len: u32) {
    for i in 0..len {
        *(dest + i as i32) = *(src + i as i32);
    }
}