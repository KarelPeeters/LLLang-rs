use win32;

// TODO why can't we use win32::HANDLE here?
static HEAP: &void = null;
static HEAP_INIT: bool = false;

fn init_heap() {
    // TODO add boolean not operator
    if !HEAP_INIT {
        HEAP = win32::GetProcessHeap();
        HEAP_INIT = true;
    }
}

fn malloc(size: usize) -> &void {
    init_heap();
    return win32::HeapAlloc(HEAP, 0, size);
}

fn free(mem: &void) -> bool {
    init_heap();
    return win32::HeapFree(HEAP, 0, mem) != 0;
}

/// overlapping memory is undefined behavior
fn memcpy(dest: &u8, src: &u8, len: usize) {
    for i in 0..len {
        // TODO switch to unsigned for ptr offset? does it even matter?
        *(dest + i as isize) = *(src + i as isize);
    }
}