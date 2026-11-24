// Borrowed string slices: a `&str` is a view of the UTF-8 bytes it refers
// to, read through the core `str` methods.

pub fn byte_len(s: &str) -> usize {
    s.len()
}

pub fn blank(s: &str) -> bool {
    s.is_empty()
}

pub fn longer(a: &str, b: &str) -> bool {
    byte_len(a) > b.len()
}

pub fn width(s: &str) -> usize {
    if s.is_empty() { 1 } else { s.len() }
}
