// The contracts of the Rust `str` core methods, one `fn` per method: a call
// of `s.len()` on a `&str` in imported Rust is a call of `str::len`. A
// `&str` is a shared slice of the UTF-8 bytes it refers to, so each
// contract states its method over that slice; `as_bytes` gives the same
// slice at the byte slice type (`click::rust::str::as_bytes`). This file is
// not a module: the Rust importer appends to a sidecar the contract of each
// method an import calls, and only those, so each stays on one line.

fn str::len(s: &str) -> usize { ensures result == s.len(); }
fn str::is_empty(s: &str) -> bool { ensures result == (s.len() == 0u64); }
fn str::as_bytes(s: &str) -> &[u8] { ensures result == click::rust::str::as_bytes(s); }
