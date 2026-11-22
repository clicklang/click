# A selected nonempty range generates its remaining guard obligations

```click
function tally(lo: int32, hi: int32) -> Integer {
    (lo..hi).fold(0, |acc, k| { acc + 1 })
}
theorem tally_append(lo: int32, hi: int32) {
    requires 0 < hi;
    requires to_integer(lo) <= to_integer(hi - 1);
    ensures tally(lo, hi) == tally(lo, hi - 1) + 1 by {
        unfold(tally(lo, hi));
        known();
    }
}
```

```expect
pass
```
