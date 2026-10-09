verifying "split.rs";
fn left_length(bytes: &[u8], mid: usize) -> usize {
    requires bytes.len() == 0u64;
    requires mid == 0u64;
    ensures result == 0u64;
} by { execute(); simp(); }
fn right_length(bytes: &[u8], mid: usize) -> usize {
    requires bytes.len() == 0u64;
    requires mid == 0u64;
    ensures result == 0u64;
} by { execute(); simp(); }
