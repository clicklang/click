pub fn sum(bytes: &[u8]) -> i32 {
    let mut total = 0i32;
    for byte in bytes.iter() {
        total += *byte as i32;
    }
    total
}
