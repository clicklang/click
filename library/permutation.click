function count<T>(p: T*, lo: int32, hi: int32, x: T) -> int32 {
    (lo..hi).fold(0, |acc, k| {
        acc + if p[k] == x { 1 } else { 0 }
    })
}

predicate permutation(a: int32[], b: int32[], lo: int32, hi: int32) {
    forall (x: int32) {
        permutation::count(a, lo, hi, x) == permutation::count(b, lo, hi, x)
    }
}
