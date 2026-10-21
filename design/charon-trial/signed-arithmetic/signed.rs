pub fn half(x: i32) -> i32 {
    x / 2
}

pub fn modulo(x: i64, y: i64) -> i64 {
    x % y
}

pub fn quotient8(x: i8, y: i8) -> i8 {
    x / y
}

pub fn remainder16(x: i16, y: i16) -> i16 {
    x % y
}

pub fn negate(x: i16) -> i16 {
    -x
}

pub fn negate32(x: i32) -> i32 {
    -x
}

pub fn mask(x: i32, y: i32) -> i32 {
    x & y
}

pub fn toggle(x: i32, y: i32) -> i32 {
    x ^ y
}

pub fn either(x: isize, y: isize) -> isize {
    x | y
}

pub fn complement(x: i64) -> i64 {
    !x
}

pub fn split(total: &mut isize, parts: isize) {
    *total /= parts;
}

pub fn shift_left(x: i32, n: u32) -> i32 {
    x << n
}

pub fn shift_right(x: i64, n: i32) -> i64 {
    x >> n
}

pub fn shift_narrow(x: i8, n: u32) -> i8 {
    (x << n) >> n
}
