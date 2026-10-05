pub fn first_byte(bytes: &[u8]) -> u8 {
    for &byte in bytes { return byte; }
    0
}
pub fn first_signed(values: &[i32]) -> i32 {
    for &value in values { return value; }
    0
}
pub fn first_unsigned(values: &[u32]) -> u32 {
    for &value in values { return value; }
    0
}
pub fn forward_signed(values: &[i32]) -> i32 { first_signed(values) }
