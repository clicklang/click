fn shift(f: &dyn Fn(i32) -> i32, x: i32, k: i32) -> i32 {
    if k == 0 { x } else { f(x) }
}

pub fn caller(k: i32, x: i32) -> i32 {
    shift(&|y| y + k, x, k)
}
