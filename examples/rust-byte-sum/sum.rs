pub fn sum(bytes: &[u8]) -> i32 {
    let mut total = 0i32;
    let mut i = 0usize;
    while i < bytes.len() {
        total += bytes[i] as i32;
        i += 1;
    }
    total
}
