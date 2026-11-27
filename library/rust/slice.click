// Rust's slices, `&[T]` and `&mut [T]`. A slice is a built-in value, a wide
// pointer: its data pointer and its length, as one value
// (`design/rust-slice-values.md`). `Slice<T>` names the type, and `Str` the
// type of `&str`. A Rust sidecar writes them with Rust's own syntax
// (`s.len()`, `s.as_ptr()`, `s[i]`, `s[a..b]`); these are what those forms
// mean. `==` on slices is identity: the same data pointer and the same
// length. Reading `s[i]` reads memory through `as_ptr(s)` under the caller's
// `views` or `owns`; a slice value grants no access.
//
// The operations below have no definition in smaller terms: each is a
// component or the constructor of the built-in value, read in place.

// The number of elements, Rust's `s.len()`.
function len<T>(s: Slice<T>) -> uint64;

// The data pointer, Rust's `s.as_ptr()`.
function as_ptr<T>(s: Slice<T>) -> T*;

// The slice with data `p` and length `n`, Rust's
// `core::slice::from_raw_parts(p, n)`. `len(from_raw_parts(p, n))` is `n`
// and `as_ptr(from_raw_parts(p, n))` is `p`.
function from_raw_parts<T>(p: T*, n: uint64) -> Slice<T>;

// The subslice `s[start..end]`: the slice with data `as_ptr(s) + start` and
// length `end - start`. A subslice requires `start <= end <= len(s)`, where
// Rust panics otherwise, so a proof that writes one owes those bounds where
// it is evaluated.
function subslice<T>(s: Slice<T>, start: uint64, end: uint64) -> Slice<T>;
