verifying "strs.rs";

// A `&str` is a shared slice of its UTF-8 bytes: a contract reads its
// length in bytes as `s.len()`, as the code does. The library states
// `str::len` and `str::is_empty` over that length.
fn str_views::byte_len(s: &str) -> usize {
    ensures result == s.len();
}

fn str_views::blank(s: &str) -> bool {
    ensures result == (s.len() == 0u64);
}

// A call passes the string slice on, and the callee's contract gives its
// length.
fn str_views::longer(a: &str, b: &str) -> bool {
    ensures result == (a.len() > b.len());
}

// `is_empty` decides the branch, so each case gives its own result.
fn str_views::width(s: &str) -> usize {
    ensures s.len() == 0u64 implies result == 1u64;
    ensures s.len() != 0u64 implies result == s.len();
}
