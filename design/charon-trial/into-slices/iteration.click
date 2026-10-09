verifying "iteration.rs";
fn first_byte(bytes: &[u8]) -> u8 {
    requires bytes.len() == 1u64;
    views bytes[0..1];
    ensures result == old(bytes[0]);
} by { execute(); simp(); }
fn first_signed(values: &[i32]) -> i32 {
    requires values.len() == 1u64;
    views values[0..1];
    ensures result == old(values[0]);
} by { execute(); simp(); }
fn first_unsigned(values: &[u32]) -> u32 {
    requires values.len() == 1u64;
    views values[0..1];
    ensures result == old(values[0]);
} by { execute(); simp(); }
fn forward_signed(values: &[i32]) -> i32 {
    requires values.len() == 1u64;
    views values[0..1];
    ensures result == old(values[0]);
} by { execute(); simp(); }
