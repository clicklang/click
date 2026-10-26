# arithmetic using reads unsigned type ranges

An unsigned value is at least zero. `arithmetic() using` cites that range for
each unsigned value the goal or a listed premise names, so a listed premise
`k < x` with `x == 0u64` is a contradiction: it proves `false`, and any goal.
The range is spelled from the written operand, whether a variable or a call.

```click
function tmp_len(j: int32) -> uint64 {
    if j == 0 { 0u64 } else { (uint64) j + 1u64 }
}

theorem below_zero_is_false(k: uint64, x: uint64) {
    requires k < x;
    requires x == 0u64;
    ensures false by { solve() using { k < x; x == 0u64; }; }
}

theorem below_an_empty_call_is_false(k: uint64, j: int32) {
    requires k < tmp_len(j);
    requires tmp_len(j) == 0u64;
    ensures false by { solve() using { k < tmp_len(j); tmp_len(j) == 0u64; }; }
}

theorem below_an_empty_call_proves_any_order(k: uint64, j: int32) {
    requires k < tmp_len(j);
    requires tmp_len(j) == 0u64;
    ensures k < 0u64 by { solve() using { k < tmp_len(j); tmp_len(j) == 0u64; }; }
}
```

```expect
pass
```
