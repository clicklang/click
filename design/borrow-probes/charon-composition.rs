pub struct Guard<'a> {
    pub slot: &'a mut u16,
    pub saved: u16,
}
impl Drop for Guard<'_> {
    fn drop(&mut self) {
        *self.slot = self.saved;
    }
}

pub fn combined(bytes: &[u8], slot: &mut u16, early: bool) -> u32 {
    let saved = *slot;
    let guard = Guard { slot, saved };
    *guard.slot += 1;
    let mut sum = u32::from(*guard.slot);
    let mut lanes = [0u32; 4];
    let mut chunks = bytes.chunks_exact(4);
    let tail = chunks.remainder();
    for chunk in &mut chunks {
        lanes[0] += u32::from(chunk[0]);
        lanes[1] += u32::from(chunk[1]);
        sum += lanes[0] + lanes[1];
    }
    for &byte in tail.iter() {
        sum += u32::from(byte);
    }
    if early {
        return sum;
    }
    let moved = guard;
    core::mem::drop(moved);
    sum
}

pub fn repeat_large() -> u8 {
    let bytes = [7u8; 1_000_000];
    bytes[999_999]
}
pub fn bump(value: u16) -> u16 {
    value + 1
}
pub fn at(bytes: &[u8], index: usize) -> u8 {
    bytes[index]
}
pub fn quotient(value: u32, divisor: u32) -> u32 {
    value / divisor
}
pub fn shifted(value: u16, count: usize) -> u16 {
    value << count
}

pub struct U32X4(pub [u32; 4]);
impl core::ops::AddAssign<Self> for U32X4 {
    fn add_assign(&mut self, other: Self) {
        self.0[0] += other.0[0];
        self.0[1] += other.0[1];
        self.0[2] += other.0[2];
        self.0[3] += other.0[3];
    }
}
pub fn lanes(mut left: U32X4, right: U32X4) -> u32 {
    left += right;
    let mut total = 0;
    for &value in left.0.iter() {
        total += value;
    }
    total
}
