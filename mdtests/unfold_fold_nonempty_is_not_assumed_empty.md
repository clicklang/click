# A nonempty fold cannot unfold to its initial value

```click
function tally(lo: int32, hi: int32) -> Integer {
    (lo..hi).fold(0, |acc, k| { acc + 1 })
}
theorem false_empty_tally(lo: int32, hi: int32) {
    requires 0 <= lo;
    requires lo < hi;
    ensures tally(lo, hi) == 0 by {
        unfold(tally(lo, hi));
        close();
    }
}
```

```expect
fail: could not establish `((tally(lo, (hi - 1)) + 1) : Integer) == 0`
```
