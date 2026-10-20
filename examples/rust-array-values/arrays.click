verifying "arrays.rs";

fn literal() -> u32 { ensures result == 5u32; } by { execute(); simp(); }
fn repeated(value: u8) -> u8 { ensures result == value; } by { execute(); simp(); }
fn independent() -> i32 { ensures result == 8; } by { execute(); simp(); }
fn replace() -> u32 { ensures result == 8u32; } by { execute(); simp(); }
fn copy_reference(words: &[u32; 2]) -> u32 {
    views words[0..2];
    ensures result == words[0];
} by { execute(); simp(); }
fn copy_into(target: &mut [u32; 2], source: &[u32; 2]) {
    owns target[0..2];
    views source[0..2];
    ensures target[0] == old(source[0]);
    ensures target[1] == old(source[1]);
} by { execute(); simp(); }
fn zero() -> usize { ensures result == 0u64; } by { execute(); simp(); }

fn next(value: &mut u32) -> u32 {
    requires *value < 255u32;
    owns value[0..1];
    ensures result == old(*value);
    ensures *value == old(*value) + 1u32;
} by { execute(); simp(); }
fn repeat_call(value: &mut u32) -> u32 {
    requires *value == 4u32;
    owns value[0..1];
    ensures result == 4u32;
    ensures *value == 5u32;
} by { execute(); simp(); }
fn zero_repeat_call(value: &mut u32) -> usize {
    requires *value == 4u32;
    owns value[0..1];
    ensures result == 0u64;
    ensures *value == 5u32;
} by { execute(); simp(); }
fn ordered_calls(value: &mut u32) -> u32 {
    requires *value == 4u32;
    owns value[0..1];
    ensures result == 5u32;
    ensures *value == 6u32;
} by { execute(); simp(); }
fn borrow_local() -> u32 { ensures result == 10u32; } by { execute(); simp(); }
fn first_arg(first: u32, _second: u32) -> u32 { ensures result == first; } by { execute(); simp(); }
fn argument_order(value: &mut u32) -> u32 {
    requires *value == 4u32;
    owns value[0..1];
    ensures result == 4u32;
    ensures *value == 5u32;
} by { execute(); simp(); }
fn self_copy() -> u8 { ensures result == 2; } by { execute(); simp(); }
fn assignment_order(value: &mut u32) -> u32 {
    requires *value == 4u32;
    owns value[0..1];
    ensures result == 4u32;
    ensures *value == 5u32;
} by { execute(); simp(); }
