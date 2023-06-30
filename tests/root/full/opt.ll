// TEST: exit 2
fn main() -> u32 {
    let a: [u32; 2];
    a[0] = 1;
    a[1] = 2;

    // tricky alias analysis
    let x = a[1];
    *((&a[0]) as &u64) = 0;
    let y = a[1];

    return x + y;
}

// TEST: exit 1
fn main() -> u32 {
    return (4u32 < __obscure(5)) ? 1 : 0;
}

// TEST: exit 5
fn foo() -> u32 {
    return 5;
}

fn main() -> u32 {
    return __obscure(foo)();
}

// TEST: exit 1
fn main() -> u32 {
    let a = false;
    let b = __obscure(&a);

    if *b == false {
        *b = true;
    }
    return *b ? 1 : 0;
}
