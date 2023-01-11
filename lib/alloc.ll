use win32;

fn malloc(size: usize) -> &void {
    let heap = win32::_GetProcessHeap@0();
    return win32::_HeapAlloc@12(heap, 0, size);
}

fn free(mem: &void) -> bool {
    let heap = win32::_GetProcessHeap@0();
    return win32::_HeapFree@12(heap, 0, mem) != 0;
}

/// overlapping memory is undefined behavior
fn memcpy(dest: &u8, src: &u8, len: usize) {
    for i in 0..len {
        // TODO switch to unsigned for ptr offset? does it even matter?
        *(dest + i as isize) = *(src + i as isize);
    }
}