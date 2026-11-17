# The removed fold tactic is rejected

```click
function total(n: int32) -> Integer {
    (0..n).fold(0, |acc, k| { acc + 1 })
}
theorem empty(n: int32) {
    requires n <= 0;
    ensures total(n) == 0 by {
        peel(total(n)) using { n <= 0; };
    }
}
```

```expect
fail: unknown tactic `peel`
```
