// The Rust wrapping functions of the cross-language integer fixture, which
// Charon does not import yet: outside the crate, so integers.rs imports.

pub fn wrapping_add_u32(a: u32, b: u32) -> u32 {
    a.wrapping_add(b)
}

pub fn wrapping_sub_u32(a: u32, b: u32) -> u32 {
    a.wrapping_sub(b)
}

pub fn wrapping_mul_u32(a: u32, b: u32) -> u32 {
    a.wrapping_mul(b)
}

pub fn wrapping_add_u64(a: u64, b: u64) -> u64 {
    a.wrapping_add(b)
}
