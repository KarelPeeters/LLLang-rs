use alloc::malloc;
use alloc::free;
use alloc::memcpy;
use print::print_str;
use print::print_int;

struct Vec {
    buf: &u8,
    cap: usize,
    len: usize,
}

fn vec_new() -> Vec {
    return Vec {
        buf: null,
        cap: 0,
        len: 0,
    };
}

fn vec_clear(vec_ptr: &Vec) {
    let vec = *vec_ptr;
    free(vec.buf as &void);
    *vec_ptr = vec_new();
}

fn vec_ensure_space(vec_ptr: &Vec, space: usize) {
    let vec = *vec_ptr;

    if vec.cap - vec.len < space {
        let cap_min = vec.len + space;
        let cap_double = 2 * vec.len;
        let new_cap = cap_min > cap_double ? cap_min : cap_double;

        let new_buf = malloc(new_cap) as &u8;

        memcpy(new_buf, vec.buf, vec.len);
        free(vec.buf as &void);

        vec.cap = new_cap;
        vec.buf = new_buf;
    }

    *vec_ptr = vec;
}

fn vec_push(vec_ptr: &Vec, value: u8) {
    let vec = *vec_ptr;

    vec_ensure_space(&vec, 1);
    *(vec.buf + vec.len as isize) = value;
    vec.len = vec.len + 1;

    *vec_ptr = vec;
}

fn print_vec(vec_ptr: &Vec) {
    let vec = *vec_ptr;

    print_str("[", 1);
    for i in 0..vec.len {
        if i != 0 {
            print_str(", ", 2);
        }

        let value = *(vec.buf + i as isize) as i64;
        print_int(value);
    }
    print_str("]", 1);
}
