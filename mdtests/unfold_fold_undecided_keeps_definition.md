# An undecided range still exposes its raw definition

```click
function tally(lo: int32, hi: int32) -> Integer {
    (lo..hi).fold(0, |acc, k| { acc + 1 })
}
theorem tally_definition(lo: int32, hi: int32) {
    ensures tally(lo, hi) == (lo..hi).fold(to_integer(0), |acc, k| { acc + 1 }) by {
        unfold(tally(lo, hi));
        known();
    }
}
```

```expect
pass
```
