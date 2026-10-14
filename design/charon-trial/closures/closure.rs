fn apply(f: fn(i32) -> i32, x: i32) -> i32 {
    f(x)
}

pub fn caller(x: i32) -> i32 {
    apply(|y| y + y, x)
}

pub fn choose(by_sum: bool, x: i32) -> i32 {
    if by_sum {
        apply(|y| y + y, x)
    } else {
        apply(|z| z * 2, x)
    }
}
