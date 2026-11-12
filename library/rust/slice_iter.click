import click::rust::slice;

// Rust's `core::slice::Iter<T>`, the iterator `s.iter()` returns, as a
// primitive type of the Click library. An iterator value stands for the
// elements it will still yield, which are a slice: `as_slice(it)`, Rust's
// `it.as_slice()`. Its meaning is the functions below and the axioms that
// relate them (`design/rust-iterators.md`).
//
// Each axiom is trusted, not proved. Rust's own `Iter` satisfies all of
// them together, so they are consistent.
//
// What one `next()` leaves is stated where the call is made, for the
// element type it is made at: the remaining slice starts one element later
// and is one shorter. An offset from a `T*` needs `T`'s size, which a
// generic axiom does not have.
type SliceIter<T>;

// The iterator `s.iter()`.
function iter<T>(s: Slice<T>) -> SliceIter<T>;

// The elements `it` will still yield, Rust's `it.as_slice()`. The next
// `next()` returns a reference to its first element.
function as_slice<T>(it: SliceIter<T>) -> Slice<T>;

// The number of elements `it` will still yield, Rust's `it.len()`.
function len<T>(it: SliceIter<T>) -> uint64;

// `it` after one `next()` that returned an element, for an `it` with
// `0 < len(it)`.
function after_next<T>(it: SliceIter<T>) -> SliceIter<T>;

// A new iterator will yield the whole slice.
axiom as_slice_iter<T>(s: Slice<T>) {
    ensures slice_iter::as_slice(slice_iter::iter(s)) == s;
}

// The count is the length of what is left.
axiom len_as_slice<T>(it: SliceIter<T>) {
    ensures slice_iter::len(it) == slice::len(slice_iter::as_slice(it));
}
