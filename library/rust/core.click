// The contracts of the Rust core and alloc methods an import calls, as
// generic `extern fn` blocks over their type parameters. This file is not
// a module: the Rust importer appends it to a sidecar when an import calls
// one of its methods, and each block is written out at each type a
// call names, `Vec::push<u32>`, as a sidecar's generic function is. A block
// no call names is dropped. An instance takes its declaration's parameter
// names by position.
//
// The `Vec` contracts state each call's effect on the library's `Vec<T>`
// value (`library/rust/vec.click`). A vector holds at most `u64::MAX`
// elements, the length `vec::len` can state, and `push` requires room below
// it; Rust's own bound is smaller (a vector of `u8` holds at most
// `isize::MAX` elements), so a proof that meets this requirement is sound
// only up to Rust's allocation limit, which aborts rather than returns.

extern fn Vec::new<T>() -> Vec<T> {
    ensures click::rust::vec::len(result) == 0u64;
}

// The capacity is outside the model: the vector is empty.
extern fn Vec::with_capacity<T>(capacity: usize) -> Vec<T> {
    ensures click::rust::vec::len(result) == 0u64;
}

// The new value, and what the library's axioms say of it, so a caller
// reads the length and elements without citing them.
extern fn Vec::push<T>(v: &mut Vec<T>, x: T) {
    owns *v;
    requires click::rust::vec::len(*v) < 18446744073709551615u64;
    ensures *v == click::rust::vec::push(old(*v), x);
    ensures click::rust::vec::len(*v) == click::rust::vec::len(old(*v)) + 1;
    ensures click::rust::vec::get(*v, click::rust::vec::len(old(*v))) == x;
    ensures forall (k: usize) { k < click::rust::vec::len(old(*v)) implies click::rust::vec::get(*v, k) == click::rust::vec::get(old(*v), k) };
}

extern fn Vec::len<T>(v: &Vec<T>) -> usize {
    views *v;
    ensures result == click::rust::vec::len(old(*v));
}

// Rust panics unless the index is in bounds.
extern fn Vec::index<T>(v: &Vec<T>, i: usize) -> T {
    views *v;
    requires i < click::rust::vec::len(*v);
    ensures result == click::rust::vec::get(old(*v), i);
}

// `<[T]>::swap(s, a, b)`: it owns the slice, Rust panics unless both
// indices are in bounds, and the two elements are exchanged while every
// other element is unchanged.
extern fn slice::swap<T>(s: &mut [T], a: usize, b: usize) {
    owns *s;
    requires a < s.len();
    requires b < s.len();
    ensures s[a] == old(s[b]);
    ensures s[b] == old(s[a]);
    ensures forall (k: usize) { k < s.len() and k != a and k != b implies s[k] == old(s[k]) };
}

// `Option::unwrap(o)` and `Option::expect(o, message)`: Rust panics unless
// `o` is `Some`, whose payload is the result. `expect`'s message serves the
// panic alone and is not passed.
extern fn Option::unwrap<T>(o: Option<T>) -> T {
    requires o != Option<T>::None;
    ensures o == Option<T>::Some(result);
}

extern fn Option::expect<T>(o: Option<T>) -> T {
    requires o != Option<T>::None;
    ensures o == Option<T>::Some(result);
}

// `Option::unwrap_or(o, d)` is the library's `option::unwrap_or`.
extern fn Option::unwrap_or<T>(o: Option<T>, d: T) -> T {
    ensures result == click::option::unwrap_or(o, d);
}

// `Result::unwrap(r)` and `Result::expect(r, message)`: Rust panics unless
// `r` is `Ok`, whose payload is the result.
extern fn Result::unwrap<T, E>(r: Result<T, E>) -> T {
    requires exists (value: T) { r == Result<T, E>::Ok(value) };
    ensures r == Result<T, E>::Ok(result);
}

extern fn Result::expect<T, E>(r: Result<T, E>) -> T {
    requires exists (value: T) { r == Result<T, E>::Ok(value) };
    ensures r == Result<T, E>::Ok(result);
}

// `Result::unwrap_or(r, d)` is the library's `result::unwrap_or`.
extern fn Result::unwrap_or<T, E>(r: Result<T, E>, d: T) -> T {
    ensures result == click::result::unwrap_or(r, d);
}

// A slice the library-iterator model returns, a chunk or a remainder, is one
// value of the library's `Slice<T>` (`library/rust/slice.click`); the body
// reads its data and length through Rust's own `<[T]>::as_ptr` and
// `<[T]>::len`.
extern fn slice::as_ptr<T>(s: Slice<T>) -> &T {
    ensures result == click::rust::slice::as_ptr(s);
}

extern fn slice::len<T>(s: Slice<T>) -> usize {
    ensures result == click::rust::slice::len(s);
}

// A slice iterator over the library's `SliceIter<T>`
// (`library/rust/slice_iter.click`): `<[T]>::iter` builds the library value
// of the slice, and `Iterator::next` is the next law over `old(*it)` and
// `*it`. Where the remaining slice starts after one `next()` needs the
// element's size, so it is stated here and written out at each element
// type, not as a generic axiom.
extern fn SliceIter::iter<T>(p: &T, n: usize) -> SliceIter<T> {
    ensures result == click::rust::slice_iter::iter(Slice<T>::Slice(p, n));
    ensures click::rust::slice::as_ptr(click::rust::slice_iter::as_slice(result)) == p;
    ensures click::rust::slice::len(click::rust::slice_iter::as_slice(result)) == n;
    ensures click::rust::slice_iter::len(result) == n;
}

extern fn SliceIter::next<T>(it: &mut SliceIter<T>) -> Option<&T> {
    owns *it;
    ensures click::rust::slice_iter::len(old(*it)) == 0u64 implies result == Option<&T>::None;
    ensures click::rust::slice_iter::len(old(*it)) == 0u64 implies *it == old(*it);
    ensures 0u64 < click::rust::slice_iter::len(old(*it)) implies result == Option<&T>::Some(click::rust::slice::as_ptr(click::rust::slice_iter::as_slice(old(*it))));
    ensures 0u64 < click::rust::slice_iter::len(old(*it)) implies *it == click::rust::slice_iter::after_next(old(*it));
    ensures 0u64 < click::rust::slice_iter::len(old(*it)) implies click::rust::slice::as_ptr(click::rust::slice_iter::as_slice(*it)) == click::rust::slice::as_ptr(click::rust::slice_iter::as_slice(old(*it))) + 1u64;
    ensures 0u64 < click::rust::slice_iter::len(old(*it)) implies click::rust::slice::len(click::rust::slice_iter::as_slice(*it)) == click::rust::slice::len(click::rust::slice_iter::as_slice(old(*it))) - 1u64;
    ensures 0u64 < click::rust::slice_iter::len(old(*it)) implies click::rust::slice_iter::len(*it) == click::rust::slice_iter::len(old(*it)) - 1u64;
}

// `<[T]>::chunks_exact` over the library's `ChunksExact<T>`
// (`library/rust/chunks_exact.click`). The importer declares these at `u8`
// only, the element type the library's chunk axioms state. Rust panics on a
// zero chunk size.
extern fn ChunksExact::new<T>(s: &[T], n: usize) -> ChunksExact<T> {
    requires n != 0u64;
    ensures result == click::rust::chunks_exact::chunks_exact(Slice<T>::Slice(s, s.len()), n);
}

// Rust's `Iterator::next` over the library value: the first chunk still to
// come, and the iterator after it. A loop over the iterator calls it in the
// library-iterator model.
extern fn ChunksExact::next<T>(it: &mut ChunksExact<T>) -> Option<&[T]> {
    owns *it;
    ensures click::rust::chunks_exact::len(old(*it)) == 0u64 implies result == Option<&[T]>::None;
    ensures click::rust::chunks_exact::len(old(*it)) == 0u64 implies *it == old(*it);
    ensures 0u64 < click::rust::chunks_exact::len(old(*it)) implies result == Option<&[T]>::Some(click::rust::chunks_exact::nth(old(*it), 0u64));
    ensures 0u64 < click::rust::chunks_exact::len(old(*it)) implies *it == click::rust::chunks_exact::after_next(old(*it));
}

extern fn ChunksExact::remainder<T>(it: &ChunksExact<T>) -> Slice<T> {
    views *it;
    ensures result == click::rust::chunks_exact::remainder(old(*it));
}

// Without the library-iterator model, a slice is still a pointer and a
// length, and the iterator a value its operations take and return: a chunk
// and the remainder are each read as their data and their length.
extern fn ChunksExact::remainder_ptr<T>(it: ChunksExact<T>) -> &T {
    ensures result == click::rust::slice::as_ptr(click::rust::chunks_exact::remainder(it));
}

extern fn ChunksExact::remainder_len<T>(it: ChunksExact<T>) -> usize {
    ensures result == click::rust::slice::len(click::rust::chunks_exact::remainder(it));
}

extern fn ChunksExact::len<T>(it: ChunksExact<T>) -> usize {
    ensures result == click::rust::chunks_exact::len(it);
}

extern fn ChunksExact::item_ptr<T>(it: ChunksExact<T>) -> &T {
    requires 0u64 < click::rust::chunks_exact::len(it);
    ensures result == click::rust::slice::as_ptr(click::rust::chunks_exact::nth(it, 0u64));
}

extern fn ChunksExact::item_len<T>(it: ChunksExact<T>) -> usize {
    requires 0u64 < click::rust::chunks_exact::len(it);
    ensures result == click::rust::slice::len(click::rust::chunks_exact::nth(it, 0u64));
}

extern fn ChunksExact::after_next<T>(it: ChunksExact<T>) -> ChunksExact<T> {
    requires 0u64 < click::rust::chunks_exact::len(it);
    ensures result == click::rust::chunks_exact::after_next(it);
}
