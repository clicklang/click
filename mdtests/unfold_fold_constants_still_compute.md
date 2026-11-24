# Constant folds expose one range step at a time

```click
function tally(lo: int32, hi: int32) -> Integer {
    (lo..hi).fold(0, |acc, k| { acc + 1 })
}
theorem empty_tally() {
    ensures tally(0, 0) == 0 by { unfold(tally(0, 0)); close(); }
}
theorem one_tally() {
    ensures tally(0, 1) == 1 by { unfold(tally(0, 1)); unfold(tally(0, 0)); close(); }
}
theorem two_tally() {
    ensures tally(0, 2) == 2 by { unfold(tally(0, 2)); unfold(tally(0, 1)); unfold(tally(0, 0)); close(); }
}
```

```expect
pass
```
