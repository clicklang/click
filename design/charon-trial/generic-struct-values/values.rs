pub fn peek<T: Copy>(value: &T) -> T {
    *value
}

pub fn put<T: Copy>(slot: &mut T, value: T) {
    *slot = value;
}

pub fn exchange<T: Copy>(left: &mut T, right: &mut T) {
    let held = *left;
    *left = *right;
    *right = held;
}

#[derive(Clone, Copy)]
pub struct Pair {
    pub x: u32,
    pub y: u32,
}

pub fn swap_pairs(a: &mut Pair, b: &mut Pair) -> u32 {
    exchange(a, b);
    put(a, peek(b));
    a.x
}

pub fn copy_pair(dst: &mut Pair, src: &Pair) {
    dst.x = src.x;
    dst.y = src.y;
}

pub fn copy_first(dst: &mut Pair, src: &Pair) {
    dst.x = src.x;
}
