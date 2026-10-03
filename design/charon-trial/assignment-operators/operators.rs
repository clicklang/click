use core::ops::{AddAssign, MulAssign, RemAssign};

pub struct U32X4(pub [u32; 4]);

impl RemAssign<u32> for U32X4 {
    #[inline]
    fn rem_assign(&mut self, quotient: u32) {
        self.0[0] %= quotient;
        self.0[1] %= quotient;
        self.0[2] %= quotient;
        self.0[3] %= quotient;
    }
}

impl MulAssign<u32> for U32X4 {
    #[inline]
    fn mul_assign(&mut self, rhs: u32) {
        self.0[0] *= rhs;
        self.0[1] *= rhs;
        self.0[2] *= rhs;
        self.0[3] *= rhs;
    }
}

impl AddAssign<&U32X4> for U32X4 {
    fn add_assign(&mut self, other: &U32X4) {
        self.0[0] += other.0[0];
        self.0[1] += other.0[1];
        self.0[2] += other.0[2];
        self.0[3] += other.0[3];
    }
}

pub fn scaled(words: &mut U32X4, factor: u32) {
    *words *= factor;
}
pub fn reduced(words: &mut U32X4, divisor: u32) {
    *words %= divisor;
}
pub fn added(words: &mut U32X4, other: &U32X4) {
    *words += other;
}
pub fn local(a: u32, b: u32) -> u32 {
    let mut words = U32X4([a, b, 3, 4]);
    words *= 2;
    words %= 7;
    words.0[0] ^ words.0[1]
}
