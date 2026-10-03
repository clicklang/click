// The last header assignment must also run on the final false test.
pub fn final_header(bytes: &[u8]) -> usize {
    let mut i = 0usize;
    let mut last;
    while {
        last = i;
        i < bytes.len()
    } {
        i += 1;
    }
    last
}

pub fn negated(bytes: &[u8]) -> usize {
    let mut i = 0usize;
    while !(i >= bytes.len()) {
        i += 1;
    }
    i
}
