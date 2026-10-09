# Peel at a constant range gives the defining equation

`peel` opens a range-fold law over a call. When the call's endpoints are
constants the kernel has already reduced the fold: over `0..0` it is the
initial value. There is no guard left to choose a law by, and `peel` was
refused with "this call's range is already reduced". It now gives the
defining equation, which is the law at that range.

Both index types are shown.

```click
function total(hi: int32) -> Integer {
    (0..hi).fold(0, |acc, k| { acc + to_integer(k) })
}

function wide_total(hi: uint64) -> Integer {
    (0..hi).fold(0, |acc, k| { acc + to_integer(k) })
}

theorem none() {
    ensures total(0) == 0 by {
        have 0 <= 0;
        peel(total(0)) using { 0 <= 0; }
        simp();
    }
    ensures wide_total(0u64) == 0 by {
        have 0u64 <= 0u64;
        peel(wide_total(0u64)) using { 0u64 <= 0u64; }
        simp();
    }
}
```

```expect
pass
```
