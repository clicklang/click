// Rust's `Vec<T>`, as a primitive type of the Click library. Like `uint32`,
// a `Vec<T>` has no definition in smaller terms: it is the finite sequence
// a Rust vector holds, and its meaning is the operations below and the
// axioms that relate them. A proof reads `vec::len(v)` and `vec::get(v, i)`
// as a contract reads `v.len()` and `v[i]`.
//
// Each axiom is trusted, not proved. Finite sequences of fewer than 2^64
// values satisfy all of them together, so they are consistent. A vector's
// capacity and allocation are outside the model: Rust aborts or panics when
// growing one fails, and a verified program never reads its capacity.
type Vec<T>;

// The number of values `v` holds.
function len<T>(v: Vec<T>) -> uint64;

// The value at index `i`, for an `i` below `len(v)`. At any other index it
// names some value the axioms say nothing about.
function get<T>(v: Vec<T>, i: uint64) -> T;

// `v` with `x` appended.
function push<T>(v: Vec<T>, x: T) -> Vec<T>;

// `v` with the value at index `i`, below `len(v)`, replaced by `x`.
function set<T>(v: Vec<T>, i: uint64, x: T) -> Vec<T>;

axiom len_push<T>(v: Vec<T>, x: T) {
    requires vec::len(v) < 18446744073709551615u64;
    ensures vec::len(vec::push(v, x)) == vec::len(v) + 1;
}

axiom get_push_last<T>(v: Vec<T>, x: T) {
    requires vec::len(v) < 18446744073709551615u64;
    ensures vec::get(vec::push(v, x), vec::len(v)) == x;
}

axiom get_push_kept<T>(v: Vec<T>, x: T, i: uint64) {
    requires i < vec::len(v);
    ensures vec::get(vec::push(v, x), i) == vec::get(v, i);
}

axiom len_set<T>(v: Vec<T>, i: uint64, x: T) {
    requires i < vec::len(v);
    ensures vec::len(vec::set(v, i, x)) == vec::len(v);
}

axiom get_set_same<T>(v: Vec<T>, i: uint64, x: T) {
    requires i < vec::len(v);
    ensures vec::get(vec::set(v, i, x), i) == x;
}

axiom get_set_other<T>(v: Vec<T>, i: uint64, j: uint64, x: T) {
    requires i < vec::len(v);
    requires j < vec::len(v);
    requires i != j;
    ensures vec::get(vec::set(v, i, x), j) == vec::get(v, j);
}

// Two vectors that hold the same values are the same vector.
axiom extensionality<T>(v: Vec<T>, w: Vec<T>) {
    requires vec::len(v) == vec::len(w);
    requires forall (i: uint64) { i < vec::len(v) implies vec::get(v, i) == vec::get(w, i) };
    ensures v == w;
}
