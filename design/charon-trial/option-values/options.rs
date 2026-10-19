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
