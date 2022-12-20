fn fac(n: u32) -> u32 {
    let x = 1;
    for i in 2..n+1 {
        x = x * i;
    }
    return x;
}

fn main() -> u32 {
    return fac(__blackbox(1));
}
