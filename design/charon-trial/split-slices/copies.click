verifying "copies.rs";
fn copy_right(bytes: &[u8], mid: usize) -> usize {
    requires mid <= bytes.len();
    requires mid <= 2147483647u64;
    ensures result == bytes.len() - mid;
}
fn reassign_left(bytes: &[u8], mid: usize) -> usize {
    requires mid <= bytes.len();
    requires mid <= 2147483647u64;
    ensures result == 0u64;
}
fn collision(bytes: &[u8], mid: usize) -> usize {
    requires mid <= bytes.len();
    requires mid <= 2147483647u64;
    ensures result == bytes.len() - mid;
}
