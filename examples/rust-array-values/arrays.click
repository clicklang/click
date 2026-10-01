verifying "arrays.rs";

uint32 literal() { ensures result == 5u32; } by { execute(); simp(); }
uint8 repeated(uint8 value) { ensures result == value; } by { execute(); simp(); }
int32 independent() { ensures result == 8; } by { execute(); simp(); }
uint32 replace() { ensures result == 8u32; } by { execute(); simp(); }
uint32 copy_reference(const uint32* words) {
    views words[0..2];
    ensures result == words[0];
} by { execute(); simp(); }
void copy_into(uint32* target, const uint32* source) {
    owns target[0..2];
    views source[0..2];
    ensures target[0] == old(source[0]);
    ensures target[1] == old(source[1]);
} by { execute(); simp(); }
uint64 zero() { ensures result == 0u64; } by { execute(); simp(); }

uint32 next(uint32* value) {
    requires *value < 255u32;
    owns value[0..1];
    ensures result == old(*value);
    ensures *value == old(*value) + 1u32;
} by { execute(); simp(); }
uint32 repeat_call(uint32* value) {
    requires *value == 4u32;
    owns value[0..1];
    ensures result == 4u32;
    ensures *value == 5u32;
} by { execute(); simp(); }
uint64 zero_repeat_call(uint32* value) {
    requires *value == 4u32;
    owns value[0..1];
    ensures result == 0u64;
    ensures *value == 5u32;
} by { execute(); simp(); }
uint32 ordered_calls(uint32* value) {
    requires *value == 4u32;
    owns value[0..1];
    ensures result == 5u32;
    ensures *value == 6u32;
} by { execute(); simp(); }
uint32 borrow_local() { ensures result == 10u32; } by { execute(); simp(); }
uint32 first_arg(uint32 first, uint32 _second) { ensures result == first; } by { execute(); simp(); }
uint32 argument_order(uint32* value) {
    requires *value == 4u32;
    owns value[0..1];
    ensures result == 4u32;
    ensures *value == 5u32;
} by { execute(); simp(); }
uint8 self_copy() { ensures result == 2; } by { execute(); simp(); }
uint32 assignment_order(uint32* value) {
    requires *value == 4u32;
    owns value[0..1];
    ensures result == 4u32;
    ensures *value == 5u32;
} by { execute(); simp(); }
