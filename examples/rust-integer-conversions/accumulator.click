verifying "accumulator.rs";

theorem widen_u16_successor(value: u16) {
    requires to_integer(value) <= 65534;
    ensures to_integer(((value + 1u16) as u16) as u32) == to_integer(value) + 1 by {
        have 0 <= to_integer(value) + 1;
        have to_integer(value) + 1 <= 65535;
        close() using { 0 <= to_integer(value) + 1; to_integer(value) + 1 <= 65535; };
    }
}

fn update(state: &mut Accumulator, byte: u8) {
    requires state.a == 65520;
    requires state.b == 65520;
    requires byte == 255;
    owns state.a;
    owns state.b;
    ensures state.a == 254;
    ensures state.b == 253;
}

fn widen(value: &u16) -> u32 {
    views *value;
    ensures result == old(*value as u32);
    ensures *value == old(*value);
}

fn bump(value: &mut u16) {
    requires *value <= 65534;
    owns *value;
    ensures (*value as u32) == old(*value as u32) + 1u32;
} by {
    step_until(function.exit);
    have 0 <= old(to_integer(*value)) + 1;
    have old(to_integer(*value)) <= 65534;
    have old(to_integer(*value)) + 1 <= 65535 by {
        apply(click::integer::add_le(old(to_integer(*value)), 65534, 1, 1));
    }
    have to_integer(*value as u32) == old(to_integer(*value)) + 1 by {
        have *value == (old(*value) + 1u16) as u16;
        apply(widen_u16_successor(old(*value)));
        rewrite(*value, (old(*value) + 1u16) as u16);
        close();
    }
    close();
}

fn bump_a(state: &mut Accumulator) {
    requires state.a <= 65534;
    owns state.a;
    views state.b;
    ensures (state.a as u32) == old(state.a as u32) + 1u32;
    ensures state.b == old(state.b);
} by {
    step_until(function.exit);
    have 0 <= old(to_integer(state.a)) + 1;
    have old(to_integer(state.a)) <= 65534;
    have old(to_integer(state.a)) + 1 <= 65535 by {
        apply(click::integer::add_le(old(to_integer(state.a)), 65534, 1, 1));
    }
    have to_integer(state.a as u32) == old(to_integer(state.a)) + 1 by {
        have state.a == (old(state.a) + 1u16) as u16;
        apply(widen_u16_successor(old(state.a)));
        rewrite(state.a, (old(state.a) + 1u16) as u16);
        close();
    }
    close();
}
