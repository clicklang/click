verifying "accumulator.rs";

fn update(state: &mut Accumulator, byte: u8) {
    requires state.a == 65520;
    requires state.b == 65520;
    requires byte == 255;
    owns state.a;
    owns state.b;
    ensures state.a == 254;
    ensures state.b == 253;
} by { execute(); simp(); }

fn widen(value: &u16) -> u32 {
    views *value;
    ensures result == old(*value as u32);
    ensures *value == old(*value);
} by { execute(); simp(); }

fn bump(value: &mut u16) {
    requires *value <= 65534;
    owns *value;
    ensures (*value as u32) == old(*value as u32) + 1u32;
} by { execute(); simp(); }

fn bump_a(state: &mut Accumulator) {
    requires state.a <= 65534;
    owns state.a;
    views state.b;
    ensures (state.a as u32) == old(state.a as u32) + 1u32;
    ensures state.b == old(state.b);
} by { execute(); simp(); }
