verifying "refs.rs";

fn nongeneric_refs::peek(value: &u32) -> u32 {
    views *value;
    ensures result == *value;
} by { execute(); simp(); }

fn nongeneric_refs::put(slot: &mut u32, value: u32) {
    owns *slot;
    ensures *slot == value;
} by { execute(); simp(); }

fn nongeneric_refs::exchange(left: &mut u32, right: &mut u32) {
    owns *left;
    owns *right;
    ensures *left == old(*right);
    ensures *right == old(*left);
} by { execute(); simp(); }

// The calls restore the first field's original value.
fn nongeneric_refs::use_refs(slots: &mut nongeneric_refs::Slots) -> u32 {
    owns slots.a;
    owns slots.b;
    ensures result == old(slots.a);
    ensures slots.b == old(slots.a);
} by { execute(); simp(); }
