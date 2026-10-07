verifying "copy.rs";

void __rust_q_I15_copy_after_call_I13_replace_first(uint32* words) {
    owns words[0..4];
    ensures words[0] == 5u32;
} by { execute(); simp(); }

uint32 __rust_q_I15_copy_after_call_I15_copy_after_call() {
    ensures result == 5u32;
} by { execute(); simp(); }
