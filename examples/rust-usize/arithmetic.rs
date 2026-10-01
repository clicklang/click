pub fn add(x: usize, y: usize) -> usize {
    x + y
}
pub fn sub(x: usize, y: usize) -> usize {
    x - y
}
pub fn mul(x: usize, y: usize) -> usize {
    x * y
}
pub fn div(x: usize, y: usize) -> usize {
    x / y
}
pub fn rem(x: usize, y: usize) -> usize {
    x % y
}
pub fn left(x: usize, n: usize) -> usize {
    x << n
}
pub fn right(x: usize, n: i32) -> usize {
    x >> n
}
pub fn bits(mut x: usize) -> usize {
    x ^= 18446744073709551615;
    x &= 4294967296;
    x |= 1;
    !x
}
pub fn narrow(x: usize) -> u32 {
    x as u32
}
pub fn byte(x: usize) -> u8 {
    x as u8
}
pub fn signed(x: usize) -> i32 {
    x as i32
}
pub fn widen(x: u32) -> usize {
    x as usize
}
pub fn sign_extend(x: i32) -> usize {
    x as usize
}
pub fn computed(bytes: &[u8], index: usize) -> u8 {
    bytes[index + 1]
}
pub fn length(bytes: &[u8]) -> usize {
    bytes.len() + 1
}
