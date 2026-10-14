fn twice(x: i32) -> i32 {
    x + x
}

fn apply(f: fn(i32) -> i32, x: i32) -> i32 {
    f(x)
}

pub fn caller(x: i32) -> i32 {
    apply(twice, x)
}

fn relay(f: fn(i32) -> i32, x: i32) -> i32 {
    apply(f, x)
}

pub fn forward(x: i32) -> i32 {
    relay(twice, x)
}
