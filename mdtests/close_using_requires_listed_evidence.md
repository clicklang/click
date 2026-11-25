# Cited evidence must exist

```click
theorem missing(xs: List<int32>, ys: List<int32>) {
    ensures (if xs == ys { 1 } else { 0 }) == 1 by {
        close() using { xs == ys; };
    }
}
```

```expect
fail: premise 0 is not exactly available
```
