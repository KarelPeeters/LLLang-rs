// TEST: exit 5
fn main() -> u32 {
    return 5;
}

// TEST: exit 8
fn main() -> u32 {
    let a = 5;
    let b = 3;
    return a + b;
}

// TEST: exit 9
fn main() -> u32 {
    let x = 3;
    let y = x * x;
    return y;
}

// TEST: exit 55
fn main() -> u32 {
    return foo(10+1);
}

fn foo(x: u32) -> u32 {
    let s = 0;
    for i in 0..x {
        s = s + i;
    }
    return s;
}