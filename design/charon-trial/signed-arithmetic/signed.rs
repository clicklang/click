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
