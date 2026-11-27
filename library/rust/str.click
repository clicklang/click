// Rust's string slices, `&str`. A string slice is the built-in wide pointer
// at its own type, `Str` (`design/rust-slice-values.md`, "String slices"):
// its data pointer and its length in bytes, as one value, like a byte slice
// `Slice<uint8>`, but a different type. A Rust sidecar writes the methods
// with Rust's own syntax (`s.len()`, `s.as_ptr()`, `s.as_bytes()`); these
// are what those forms mean. `==` on string slices is identity: the same
// data pointer and the same length. A string slice grants no access.
//
// Rust's `str` holds valid UTF-8. That validity is not modeled: nothing here
// states it, and nothing proved about a string's bytes depends on it.
//
// The operations below have no definition in smaller terms: each is a
// component of the built-in value, read in place, or a retyping of it.

// The length in bytes, Rust's `s.len()`.
function len(s: Str) -> uint64;

// The data pointer, Rust's `s.as_ptr()`.
function as_ptr(s: Str) -> uint8*;

// The same bytes as a byte slice, Rust's `s.as_bytes()`: the same data
// pointer and length at the type `Slice<uint8>`.
function as_bytes(s: Str) -> Slice<uint8>;

// The byte slice `v` as a string slice, Rust's
// `core::str::from_utf8_unchecked(v)`: the same data pointer and length at
// the type `Str`. Rust requires `v` to be valid UTF-8; that requirement is
// not modeled. `as_bytes(from_utf8_unchecked(v))` is `v`.
function from_utf8_unchecked(v: Slice<uint8>) -> Str;
