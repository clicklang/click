fn shift(f: &dyn Fn(i32) -> i32, x: i32, k: i32) -> i32 {
    if k == 0 { x } else { f(x) }
}

pub fn caller(k: i32, x: i32) -> i32 {
    shift(&|y| y + k, x, k)
}

pub fn moved(k: i32, x: i32) -> i32 {
    let m = k + 1;
    shift(&move |y| y + m, x, m)
}

fn increment(f: &dyn Fn(i32) -> i32, x: i32) -> i32 {
    f(x)
}

pub fn plain(x: i32) -> i32 {
    increment(&|y| y + 1, x)
}
