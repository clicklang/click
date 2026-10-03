pub struct Accumulator {
    pub a: u16,
    pub b: u16,
}

pub fn update(state: &mut Accumulator, byte: u8) {
    let mut a = u32::from(state.a);
    let mut b = u32::from(state.b);
    a += u32::from(byte);
    b += a;
    state.a = (a % 65521) as u16;
    state.b = (b % 65521) as u16;
}

pub fn widen(value: &u16) -> u32 {
    u32::from(*value)
}

pub fn bump(value: &mut u16) {
    *value += 1;
}

pub fn bump_a(state: &mut Accumulator) {
    state.a += 1;
}
