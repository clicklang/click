import click::rust::slice;

// Rust's `core::slice::ChunksExact<T>`, the iterator `s.chunks_exact(n)`
// returns, as a primitive type of the Click library. An iterator value
// stands for the finite sequence of items it will still yield: `len(it)`
// items, the `k`-th of them `nth(it, k)`. Its meaning is the functions
// below and the axioms that relate them (`design/rust-iterators.md`).
//
// Each axiom is trusted, not proved. Rust's own `ChunksExact` satisfies all
// of them together, so they are consistent. `nth` here is an observation
// that consumes nothing, not Rust's consuming `Iterator::nth`.
type ChunksExact<T>;

// The iterator `s.chunks_exact(n)`, for a chunk size `n` that is not zero,
// where Rust panics.
function chunks_exact<T>(s: Slice<T>, n: uint64) -> ChunksExact<T>;

// The number of chunks `it` will still yield, Rust's `it.len()`.
function len<T>(it: ChunksExact<T>) -> uint64;

// The chunk the `k`-th following `next()` returns, for a `k` below
// `len(it)`. At any other index it names some slice the axioms say nothing
// about.
function nth<T>(it: ChunksExact<T>, k: uint64) -> Slice<T>;

// The elements the chunks leave over, Rust's `it.remainder()`.
function remainder<T>(it: ChunksExact<T>) -> Slice<T>;

// `it` after one `next()` that returned a chunk, for an `it` with
// `0 < len(it)`.
function after_next<T>(it: ChunksExact<T>) -> ChunksExact<T>;

axiom len_chunks_exact<T>(s: Slice<T>, n: uint64) {
    requires n != 0u64;
    ensures chunks_exact::len(chunks_exact::chunks_exact(s, n)) == slice::len(s) / n;
}

// Chunk `k` is the `n` elements from element `k * n`.
axiom nth_chunks_exact<T>(s: Slice<T>, n: uint64, k: uint64) {
    requires n != 0u64;
    requires k < slice::len(s) / n;
    ensures slice::as_ptr(chunks_exact::nth(chunks_exact::chunks_exact(s, n), k))
        == slice::as_ptr(s) + k * n;
    ensures slice::len(chunks_exact::nth(chunks_exact::chunks_exact(s, n), k)) == n;
}

// The remainder is the last `len(s) % n` elements.
axiom remainder_chunks_exact<T>(s: Slice<T>, n: uint64) {
    requires n != 0u64;
    ensures slice::as_ptr(chunks_exact::remainder(chunks_exact::chunks_exact(s, n)))
        == slice::as_ptr(s) + (slice::len(s) - slice::len(s) % n);
    ensures slice::len(chunks_exact::remainder(chunks_exact::chunks_exact(s, n)))
        == slice::len(s) % n;
}

axiom len_after_next<T>(it: ChunksExact<T>) {
    requires 0u64 < chunks_exact::len(it);
    ensures chunks_exact::len(chunks_exact::after_next(it)) == chunks_exact::len(it) - 1u64;
}

axiom nth_after_next<T>(it: ChunksExact<T>, k: uint64) {
    requires 0u64 < chunks_exact::len(it);
    requires k < chunks_exact::len(it) - 1u64;
    ensures chunks_exact::nth(chunks_exact::after_next(it), k)
        == chunks_exact::nth(it, k + 1u64);
}

// `next()` leaves the remainder as it was.
axiom remainder_after_next<T>(it: ChunksExact<T>) {
    requires 0u64 < chunks_exact::len(it);
    ensures chunks_exact::remainder(chunks_exact::after_next(it)) == chunks_exact::remainder(it);
}
