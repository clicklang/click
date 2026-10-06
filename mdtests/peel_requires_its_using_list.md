# peel requires its using list

The listed guard is what selects the equation `peel` opens, so a `peel`
without a list is refused where it is written.

```click
function icount(p: int32[], lo: int32, hi: int32) -> Integer {
    (lo..hi).fold(0, |acc, k| { acc + to_integer(p[k]) })
}

theorem icount_empty(p: int32[], lo: int32, hi: int32) {
    requires hi <= lo;
    ensures icount(p, lo, hi) == 0 by {
        peel(icount(p, lo, hi));
        normalize();
    }
}
```

```expect
fail: `peel` requires a `using { ... }` list naming the guard that decides the range
```
