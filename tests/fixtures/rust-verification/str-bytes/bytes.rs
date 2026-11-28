// Byte views of string slices: `s.as_bytes()` is the same data pointer and
// length as a `&[u8]`, read with the byte slice's own methods.

pub fn byte_count(s: &str) -> usize {
    let bytes = s.as_bytes();
    bytes.len()
}

pub fn first_byte(s: &str) -> u8 {
    let bytes = s.as_bytes();
    bytes[0]
}
