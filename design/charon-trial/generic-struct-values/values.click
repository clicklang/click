verifying "values.rs";

// The generic functions over a value of `T` are verified once. A call at a
// `Copy` struct, `generic_struct_values::Pair`, takes their contracts at
// that struct: `*left == old(*right)` says the two structs hold the same
// value, every field of one equal to the same field of the other.

fn generic_struct_values::peek<T: Copy>(value: &T) -> T {
    views *value;
    ensures result == *value;
}

fn generic_struct_values::put<T: Copy>(slot: &mut T, value: T) {
    owns *slot;
    ensures *slot == value;
}

fn generic_struct_values::exchange<T: Copy>(left: &mut T, right: &mut T) {
    owns *left;
    owns *right;
    ensures *left == old(*right);
    ensures *right == old(*left);
}

fn generic_struct_values::swap_pairs(a: &mut generic_struct_values::Pair, b: &mut generic_struct_values::Pair) -> u32 {
    owns *a;
    owns *b;
    ensures result == old(a.x);
    ensures a.y == old(a.y);
    ensures b.x == old(a.x);
}

// A struct's value is all its fields: copying both makes the structs equal.
fn generic_struct_values::copy_pair(dst: &mut generic_struct_values::Pair, src: &generic_struct_values::Pair) {
    owns *dst;
    views *src;
    ensures *dst == *src;
} by {
    step_until(function.exit);
    have *dst == *src;
}

// Copying one field makes that field equal, not the structs.
fn generic_struct_values::copy_first(dst: &mut generic_struct_values::Pair, src: &generic_struct_values::Pair) {
    owns *dst;
    views *src;
    ensures dst.x == src.x;
}
