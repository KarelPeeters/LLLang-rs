// TEST: exit 1
fn main() -> u32 {
    let a = __obscure(1);
    __blackhole(&a);
    __membarrier();
    return a;
}

// TODO ensure full parse & lower coverage with this test case alone

// TEST: exit 2
fn main() -> u32 {
    return call(add_one, 1);
}

fn call(f: (u32) -> u32, x: u32) -> u32 {
    return f(x);
}

fn add_one(x: u32) -> u32 {
    return x + 1;
}