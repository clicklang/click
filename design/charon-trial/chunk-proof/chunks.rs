pub fn cover(bytes: &[u8]) -> usize {
    let chunks = bytes.chunks_exact(4);
    let tail = chunks.remainder();
    for chunk in chunks {
        let first = chunk[0];
        let last = chunk[3];
    }
    tail.len()
}
