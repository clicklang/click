pub fn first(bytes: &[u8]) -> u8 { bytes[0] }
pub fn walk(bytes: &[u8]) -> u32 {
    let iter = bytes.chunks_exact(4);
    for chunk in iter {
        let _byte = first(chunk);
    }
    0
}
