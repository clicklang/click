pub fn signed_len(values: &[i32; 1024]) -> usize {
    values.len()
}

pub fn million_len(values: &[u32; 1_000_000]) -> usize {
    values.len()
}

pub fn empty_len(values: &[u32; 0]) -> usize {
    values.len()
}
