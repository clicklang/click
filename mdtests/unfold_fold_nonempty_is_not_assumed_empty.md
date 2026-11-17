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
        normalize();
    }
}
```

```expect
fail: `normalize` goal did not normalize to true
```
