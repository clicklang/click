pub fn some_if(x: u32, make: bool) -> Option<u32> {
    if make { Some(x) } else { None }
}

pub fn or_zero(o: Option<u32>) -> u32 {
    match o {
        Some(v) => v,
        None => 0,
    }
}

pub fn round(x: u32) -> u32 {
    or_zero(some_if(x, true))
}

pub fn flag(o: Option<bool>) -> bool {
    match o {
        Some(b) => b,
        None => false,
    }
}

pub fn flagged(x: bool) -> bool {
    flag(Some(x))
}

pub fn wrap<T: Copy>(value: T) -> Option<T> {
    Some(value)
}

pub fn unwrap_or<T: Copy>(o: Option<T>, default: T) -> T {
    match o {
        Some(v) => v,
        None => default,
    }
}

pub fn defaulted(x: i32) -> i32 {
    unwrap_or(wrap(x), 0)
}
