fn add3(x: i32) -> i32 {
    x + 3
}

fn apply(f: fn(i32) -> i32, x: i32, k: i32) -> i32 {
    f(x)
}

pub fn caller(x: i32) -> i32 {
    apply(add3, x, 3)
}
