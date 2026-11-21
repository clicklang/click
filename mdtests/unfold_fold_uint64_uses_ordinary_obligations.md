# A nonempty fold proves its guards through ordinary obligations

```click
function tally(lo: uint64, hi: uint64) -> Integer {
    (lo..hi).fold(0, |acc, k| { acc + 1 })
}

theorem tally_append(lo: uint64, hi: uint64) {

    requires lo < hi;
    ensures tally(lo, hi) == tally(lo, hi - 1u64) + 1 by {
        unfold(tally(lo, hi));
        known();
    }
}
```

```expect
pass
```
