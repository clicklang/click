verifying "arrays.rs";

fn first(bytes: &[u8]) -> u8 {
    requires bytes.len() > 0u64;
    requires bytes.len() <= 2147483647u64;
    views bytes[0..1];
    ensures result == bytes[0];
} by { execute(); simp(); }
fn set(bytes: &mut [u8]) {
    requires bytes.len() > 1u64;
    requires bytes.len() <= 2147483647u64;
    owns bytes[1..2];
    ensures bytes[1] == 7;
} by { execute(); simp(); }
fn size(bytes: &[u8]) -> usize {
    ensures result == bytes.len();
} by { execute(); simp(); }
fn array_len(bytes: &[u8; 3]) -> usize { ensures result == 3u64; } by { execute(); simp(); }
fn read(bytes: &[u8; 3]) -> u8 {
    views bytes[0..1];
    ensures result == bytes[0];
} by { execute(); simp(); }
fn mutate(bytes: &mut [u8; 3]) -> u8 {
    owns bytes[1..2];
    ensures result == 7;
} by { execute(); simp(); }
fn local() -> u8 { ensures result == 10; } by { execute(); simp(); }
fn alias(bytes: &mut [u8; 3]) -> u8 {
    owns bytes[1..2];
    ensures result == 7;
} by { execute(); simp(); }
fn retarget() -> usize { ensures result == 4u64; } by { execute(); simp(); }
fn retarget_mut() -> u8 { ensures result == 14; } by { execute(); simp(); }
fn empty() -> usize { ensures result == 0u64; } by { execute(); simp(); }
fn empty_ref(bytes: &[u8; 0]) -> usize { ensures result == 0u64; } by { execute(); simp(); }
fn borrow_shared(bytes: &mut [u8; 3]) -> u8 {
    owns bytes[0..1];
    ensures result == bytes[0];
} by { execute(); simp(); }
