pub fn copy_right(bytes: &[u8], mid: usize) -> usize {
    let pair = bytes.split_at(mid);
    let copied = pair;
    copied.1.len()
}

pub fn reassign_left(bytes: &[u8], mid: usize) -> usize {
    let mut pair = bytes.split_at(mid);
    pair = bytes.split_at(0);
    pair.0.len()
}

pub fn collision(bytes: &[u8], mid: usize) -> usize {
    let pair_slice_0 = bytes;
    let pair_slice_1_len = mid;
    let pair = pair_slice_0.split_at(pair_slice_1_len);
    pair.1.len()
}
