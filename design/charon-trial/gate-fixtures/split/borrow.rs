pub fn left_length(bytes: &[u8], mid: usize) -> usize {
    let (left, right) = bytes.split_at(mid);
    left.len()
}

pub fn right_length(bytes: &[u8], mid: usize) -> usize {
    let (left, right) = bytes.split_at(mid);
    right.len()
}

pub fn left_first(bytes: &[u8], mid: usize) -> u8 {
    let (left, right) = bytes.split_at(mid);
    left[0]
}

pub fn right_first(bytes: &[u8], mid: usize) -> u8 {
    let (left, right) = bytes.split_at(mid);
    right[0]
}
