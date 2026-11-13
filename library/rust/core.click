// The contracts of the Rust core and alloc methods an import calls, as
// generic `extern fn` blocks over their element type `T`. This file is not
// a module: the Rust importer appends it to a sidecar when an import calls
// one of its methods, and each block is written out at each element type a
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
