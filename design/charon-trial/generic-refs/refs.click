verifying "refs.rs";

// A reference to a value of `T` reads and writes one value of `T`.
fn generic_refs::peek<T: Copy>(value: &T) -> T {
    views *value;
    ensures result == *value;
} by { execute(); simp(); }

fn generic_refs::put<T: Copy>(slot: &mut T, value: T) {
    owns *slot;
    ensures *slot == value;
} by { execute(); simp(); }

fn generic_refs::exchange<T: Copy>(left: &mut T, right: &mut T) {
    owns *left;
    owns *right;
    ensures *left == old(*right);
    ensures *right == old(*left);
} by { execute(); simp(); }

// The calls at `u32` use them at `&u32` and `&mut u32`, borrowed from
// fields.
fn generic_refs::use_refs(slots: &mut generic_refs::Slots) -> u32 {
    owns slots.a;
    owns slots.b;
    ensures result == old(slots.a);
    ensures slots.b == old(slots.a);
} by { execute(); simp(); }
