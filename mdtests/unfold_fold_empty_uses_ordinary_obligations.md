# An empty fold unfolds without a written guard list

```click
function tally(lo: int32, hi: int32) -> Integer {
    (lo..hi).fold(0, |acc, k| { acc + 1 })
}

theorem empty_tally(lo: int32, hi: int32) {
    requires hi < lo;
    ensures tally(lo, hi) == 0 by {
        unfold(tally(lo, hi));
        normalize();
    }
}
```

```expect
pass
```
