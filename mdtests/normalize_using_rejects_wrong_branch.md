# A checked opposite condition does not establish the wrong branch

```click
theorem wrong(xs: List<int32>, ys: List<int32>) {
    requires not(xs == ys);
    ensures (if xs == ys { 1 } else { 0 }) == 1 by {
        close() using { not(xs == ys); };
    }
}
```

```expect
fail: `close() using` could not prove the current goal from only its listed premises
```
