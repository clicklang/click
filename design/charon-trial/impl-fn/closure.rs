fn shift(f: impl Fn(i32) -> i32, x: i32, k: i32) -> i32 {
    if k == 0 { x } else { f(x) }
}

pub fn caller(k: i32, x: i32) -> i32 {
    shift(|y| y + k, x, k)
}

fn apply<F: Fn(i32) -> i32>(f: F, x: i32) -> i32 {
    f(x)
}

pub fn plain(x: i32) -> i32 {
    apply(|y| y + 1, x)
}

fn inc(y: i32) -> i32 {
    y + 1
}

pub fn named(x: i32) -> i32 {
    apply(inc, x)
}

fn both(f: impl Fn(i32) -> i32, g: impl Fn(i32) -> i32, x: i32, k: i32) -> i32 {
    g(f(x))
}

pub fn twice(k: i32, x: i32) -> i32 {
    both(|y| y + k, |y| y + 1, x, k)
}
