# A nonempty fold proves its guards through ordinary obligations

```click
function tally(lo: int32, hi: int32) -> Integer {
    (lo..hi).fold(0, |acc, k| { acc + 1 })
}

theorem tally_append(lo: int32, hi: int32) {
    requires 0 <= lo;
    requires lo < hi;
    ensures tally(lo, hi) == tally(lo, hi - 1) + 1 by {
        unfold(tally(lo, hi));
        close();
    }
}
```

```expect
pass
```
