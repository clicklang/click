verifying "iteration.rs";
fn first_byte(bytes: &[u8]) -> u8 {
    requires bytes.len() == 0u64;
    ensures result == 0;
} by { execute(); simp(); }
fn first_signed(values: &[i32]) -> i32 {
    requires values.len() == 0u64;
    ensures result == 0;
} by { execute(); simp(); }
fn first_unsigned(values: &[u32]) -> u32 {
    requires values.len() == 0u64;
    ensures result == 0u32;
} by { execute(); simp(); }
