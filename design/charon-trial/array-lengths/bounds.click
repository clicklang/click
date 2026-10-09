verifying "bounds.rs";

fn signed_len(values: &[i32; 1024]) -> usize {
    ensures result == 1024u64;
} by { execute(); simp(); }

fn million_len(values: &[u32; 1_000_000]) -> usize {
    ensures result == 1000000u64;
} by { execute(); simp(); }

fn empty_len(values: &[u32; 0]) -> usize {
    ensures result == 0u64;
} by { execute(); simp(); }
