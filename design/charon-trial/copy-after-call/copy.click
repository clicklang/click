verifying "copy.rs";

fn copy_after_call::replace_first(words: &mut [u32; 4]) {
    owns words[0..4];
    ensures words[0] == 5u32;
} by { execute(); simp(); }

fn copy_after_call::copy_after_call() -> u32 {
    ensures result == 5u32;
} by { execute(); simp(); }
