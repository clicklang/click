pub fn smaller(a: u32, b: u32) -> u32 {
    a.min(b)
}

pub fn larger(a: i64, b: i64) -> i64 {
    a.max(b)
}

pub fn clamp_add(a: u32, b: u32) -> u32 {
    match a.checked_add(b) {
        Some(sum) => sum,
        None => 0,
    }
}

pub fn shortfall(have: u32, need: u32) -> u32 {
    need.saturating_sub(have)
}

pub fn byte_ring(a: u8, b: u8) -> u8 {
    a.wrapping_add(b)
}

pub fn sample_sum(a: i16, b: i16) -> i16 {
    a.saturating_add(b)
}

pub fn distance(a: i32, b: i32) -> u32 {
    a.abs_diff(b)
}

pub fn magnitude(a: i8) -> u8 {
    a.unsigned_abs()
}

pub fn fewer(a: usize, b: usize) -> usize {
    a.min(b)
}
