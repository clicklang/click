# Renaming fold binders cannot prove an undefined machine sum

Both functions sum a range into an `int32` accumulator. For unrestricted
bounds that sum can overflow. Alpha equivalence does not establish the
definedness of either side, so the unchanged unbounded equality is refused.

```c filename=range_fold_alpha_equivalence.c
int32 range_fold_alpha_equivalence(int32 lo, int32 hi) {
    return 0;
}
```

```click
verifying "range_fold_alpha_equivalence.c";

function sum_range_a(lo: int32, hi: int32) -> int32 {
    (lo..hi).fold(0, |acc, k| {
        acc + k
    })
}

function sum_range_b(lo: int32, hi: int32) -> int32 {
    (lo..hi).fold(0, |total, i| {
        total + i
    })
}

int32 range_fold_alpha_equivalence(int32 lo, int32 hi) {
    ensures renamed_fold_binders: sum_range_a(lo, hi) == sum_range_b(lo, hi);
}
```

```expect
fail: unclosed goal: sum_range_a
```
