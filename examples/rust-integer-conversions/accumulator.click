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
    ensures result == old((uint32)*value);
    ensures *value == old(*value);
} by { execute(); simp(); }

fn bump(value: &mut u16) {
    requires *value <= 65534;
    owns *value;
    ensures ((uint32)*value) == old((uint32)*value) + 1u32;
} by { execute(); simp(); }

fn bump_a(state: &mut Accumulator) {
    requires state.a <= 65534;
    owns state.a;
    views state.b;
    ensures ((uint32)state.a) == old((uint32)state.a) + 1u32;
    ensures state.b == old(state.b);
} by { execute(); simp(); }
