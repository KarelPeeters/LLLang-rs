// TEST: exit 89
fn main() -> u32 {
    return fib(10);
}

fn fib(n: u32) -> u32 {
    let a = 1;
    let b = 1;

    for i in 0..n {
        let t = b;
        b = a + b;
        a = t;
    }

    return a;
}

// TODO recursive fib once recursion is working again

// TEST: exit 11
fn main() -> u32 {
    return next_prime(8);
}

fn next_prime(s: u32) -> u32 {
    let i = s;
    loop {
        if (is_prime(i)) {
            return i;
        }
        i = i + 1;
    }
}

fn is_prime(p: u32) -> bool {
    for i in 2..p {
        if p % i == 0 {
            return false;
        }
    }
    return true;
}

// TEST: opt, exit 29
fn main() -> u32 {
    return nth_match(10, is_prime);
}

fn nth_match(n: u32, f: (u32) -> bool) -> u32 {
    let p: u32 = 1;
    let i: u32 = 0;

    while i != n {
        p = p + 1;
        if f(p) {
            i = i + 1;
        }
    }

    return p;
}

fn is_prime(n: u32) -> bool {
    let i: u32 = 2;
    while i != n {
        if n % i == 0 {
            return false;
        }
        i = i + 1;
    }

    return true;
}

