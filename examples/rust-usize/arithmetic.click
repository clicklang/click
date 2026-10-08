verifying "arithmetic.rs";
fn add(x: usize, y: usize) -> usize {
    requires x <= 18446744073709551615u64 - y;
    ensures result == x + y;
} by { execute(); simp(); }
fn sub(x: usize, y: usize) -> usize {
    requires x >= y;
    ensures result == x - y;
} by { execute(); simp(); }
fn mul(x: usize, y: usize) -> usize {
    requires x == 4294967296u64;
    requires y == 2147483648u64;
    ensures result == 9223372036854775808u64;
} by { execute(); simp(); }
fn div(x: usize, y: usize) -> usize {
    requires y != 0u64;
    ensures result == x / y;
} by { execute(); simp(); }
fn rem(x: usize, y: usize) -> usize {
    requires y != 0u64;
    ensures result == x % y;
} by { execute(); simp(); }
fn left(x: usize, n: usize) -> usize {
    requires x == 9223372036854775808u64;
    requires n == 1u64;
    ensures result == 0u64;
} by { execute(); simp(); }
fn right(x: usize, n: i32) -> usize {
    requires x == 18446744073709551615u64;
    requires n == 63;
    ensures result == 1u64;
} by { execute(); simp(); }
fn bits(x: usize) -> usize {
    requires x == 0u64;
    ensures result == 18446744069414584318u64;
} by { execute(); simp(); }
fn narrow(x: usize) -> u32 {
    requires x == 4294967297u64;
    ensures result == 1u32;
} by { execute(); simp(); }
fn byte(x: usize) -> u8 {
    requires x == 18446744073709551615u64;
    ensures result == 255;
} by { execute(); simp(); }
fn signed(x: usize) -> i32 {
    requires x == 18446744073709551615u64;
    ensures result == -1;
} by { execute(); simp(); }
fn widen(x: u32) -> usize {
    requires x == 4294967295u32;
    ensures result == 4294967295u64;
} by { execute(); simp(); }
fn sign_extend(x: i32) -> usize {
    requires x == -1;
    ensures result == 18446744073709551615u64;
} by { execute(); simp(); }
fn computed(bytes: &[u8], index: usize) -> u8 {
    requires bytes_len == 2u64;
    requires index == 0u64;
    views bytes[0 .. 2];
    ensures result == bytes[1];
} by { execute(); simp(); }
fn length(bytes: &[u8]) -> usize {
    requires bytes_len <= 18446744073709551614u64;
    ensures result == bytes_len + 1u64;
} by { execute(); simp(); }
