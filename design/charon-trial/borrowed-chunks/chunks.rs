pub fn cover(bytes: &[u8]) -> usize {
    let mut chunks = bytes.chunks_exact(4);
    let tail = chunks.remainder();
    for chunk in &mut chunks {
        let first = chunk[0];
        let last = chunk[3];
    }
    chunks.remainder().len()
}
