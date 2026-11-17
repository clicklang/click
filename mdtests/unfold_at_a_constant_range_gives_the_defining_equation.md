# Unfold at a constant range gives the defining equation

When a call's range endpoints are constants, the kernel already reduces the
fold. Over `0..0`, ordinary `unfold` gives the initial value for both machine
index types.

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
        unfold(total(0));
        solve();
    }
    ensures wide_total(0u64) == 0 by {
        have 0u64 <= 0u64;
        unfold(wide_total(0u64));
        solve();
    }
}
```

```expect
pass
```
