// Rust's slices, `&[T]` and `&mut [T]`: the data pointer and the length a
// Rust slice carries, as one value. A Rust sidecar writes them with Rust's
// own spellings (`s.len()`, `s.as_ptr()`, `s[i]`, `s[a..b]`); these are what
// those spellings mean. `==` on slices is identity: the same data pointer and
// the same length. Reading `s[i]` reads memory through `as_ptr(s)` under the
// caller's `views` or `owns`; a slice value grants no access.
spec enum Slice<T> {
    Slice(T*, uint64),
}

// The number of elements, Rust's `s.len()`.
function len<T>(s: Slice<T>) -> uint64 {
    match s {
        Slice::Slice(_, n) => n,
    }
}

// The data pointer, Rust's `s.as_ptr()`.
function as_ptr<T>(s: Slice<T>) -> T* {
    match s {
        Slice::Slice(p, _) => p,
    }
}

// The slice with data `p` and length `n`, Rust's
// `core::slice::from_raw_parts(p, n)`.
function from_raw_parts<T>(p: T*, n: uint64) -> Slice<T> {
    Slice::Slice(p, n)
}

// The length of the subslice `s[start..end]`, `end - start`. A subslice
// requires `start <= end <= len`, where Rust panics otherwise, so a proof
// that writes one owes those bounds where it is evaluated.
function subslice_len(start: uint64, end: uint64, len: uint64) -> uint64 {
    end - start
}
