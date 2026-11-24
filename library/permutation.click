function count<T>(p: T*, lo: int32, hi: int32, x: T) -> int32 {
    (lo..hi).fold(0, |acc, k| {
        acc + if p[k] == x { 1 } else { 0 }
    })
}

// Keep the initial zero from the two-element count fold.
theorem two_indicator_counts_commute(a: Bool, b: Bool) {
    ensures (0 + (if a { 1 } else { 0 }) + (if b { 1 } else { 0 })) ==
            (0 + (if b { 1 } else { 0 }) + (if a { 1 } else { 0 })) by {
        if a {
            have (if a { 1 } else { 0 }) == 1 by close();
            rewrite((if a { 1 } else { 0 }), 1);
            if b {
                have (if b { 1 } else { 0 }) == 1 by close();
                rewrite((if b { 1 } else { 0 }), 1);
                close();
            } else {
                have (if b { 1 } else { 0 }) == 0 by close();
                rewrite((if b { 1 } else { 0 }), 0);
                close();
            }
        } else {
            have (if a { 1 } else { 0 }) == 0 by close();
            rewrite((if a { 1 } else { 0 }), 0);
            if b {
                have (if b { 1 } else { 0 }) == 1 by close();
                rewrite((if b { 1 } else { 0 }), 1);
                close();
            } else {
                have (if b { 1 } else { 0 }) == 0 by close();
                rewrite((if b { 1 } else { 0 }), 0);
                close();
            }
        }
    }
}

predicate permutation(a: int32[], b: int32[], lo: int32, hi: int32) {
    forall (x: int32) {
        permutation::count(a, lo, hi, x) == permutation::count(b, lo, hi, x)
    }
}
