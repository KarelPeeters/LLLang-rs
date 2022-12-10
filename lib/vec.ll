use math::max;
use alloc::malloc;
use alloc::free;
use alloc::memcpy;
use print::print_str;
use print::print_int;

struct Vec {
    buf: &byte,
    cap: int,
    len: int,
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

fn vec_ensure_space(vec_ptr: &Vec, space: int) {
    let vec = *vec_ptr;

    if vec.cap - vec.len < space {
        let new_cap = max(vec.len + space, 2 * vec.len);
        let new_buf: &byte = malloc(new_cap) as &byte;

        memcpy(new_buf, vec.buf, vec.len);

        vec.cap = new_cap;
        vec.buf = new_buf;
    }

    *vec_ptr = vec;
}

fn vec_push(vec_ptr: &Vec, value: byte) {
    let vec = *vec_ptr;

    vec_ensure_space(&vec, 1);
    *(vec.buf + vec.len) = value;
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

        let value_byte = *(vec.buf + i);
        let value_int = *(&value_byte as &int);
        print_int(value_int);
    }
    print_str("]", 1);
}
