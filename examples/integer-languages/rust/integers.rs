// The cross-language integer fixture's programs (tests/examples/integer_languages.rs);
// integers.c, integers.cpp and integers.rs are the same functions. The
// wrapping ones Charon does not import are in gaps.rs.

pub fn add_i32(a: i32, b: i32) -> i32 {
    a + b
}

pub fn sub_i32(a: i32, b: i32) -> i32 {
    a - b
}

pub fn mul_i32(a: i32, b: i32) -> i32 {
    a * b
}

pub fn above_int32_max() -> u32 {
    4000000000
}

pub fn keep_above_int32_max(u: u32) -> u32 {
    if u > 2147483647 {
        return u;
    }
    0
}

pub fn to_signed_i32(u: u32) -> i32 {
    u as i32
}

pub fn to_unsigned_u32(x: i32) -> u32 {
    x as u32
}

pub fn div_u32(a: u32, b: u32) -> u32 {
    a / b
}

pub fn rem_u32(a: u32, b: u32) -> u32 {
    a % b
}

pub fn shr_u32(a: u32, n: u32) -> u32 {
    a >> n
}

pub fn div_i32(a: i32, b: i32) -> i32 {
    a / b
}

pub fn rem_i32(a: i32, b: i32) -> i32 {
    a % b
}

pub fn shr_i32(a: i32, n: u32) -> i32 {
    a >> n
}

pub fn narrow_u8(x: u32) -> u8 {
    x as u8
}

pub fn narrow_i8(x: i32) -> i8 {
    x as i8
}

pub fn narrow_u8_in_range(x: u32) -> u8 {
    x as u8
}

pub fn add_i64(a: i64, b: i64) -> i64 {
    a + b
}

pub fn below_i32(a: i32, b: i32) -> bool {
    a < b
}

pub fn below_u32(a: u32, b: u32) -> bool {
    a < b
}

pub fn sign_bit_set(u: u32) -> bool {
    (u as i32) < 0
}

pub fn not_bool(b: bool) -> bool {
    !b
}

pub fn and_bool(a: bool, b: bool) -> bool {
    a && b
}

pub fn int_to_bool(x: i32) -> bool {
    x != 0
}

pub fn bool_to_u8(b: bool) -> u8 {
    b as u8
}

pub fn bool_sum(a: bool, b: bool) -> i32 {
    a as i32 + b as i32
}

pub fn select_i32(b: bool, x: i32, y: i32) -> i32 {
    if b { x } else { y }
}
