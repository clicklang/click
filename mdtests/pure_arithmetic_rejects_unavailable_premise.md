# arithmetic requires every listed premise exactly

```click
theorem omitted_bound(n: int32) {
    ensures 0 <= n - 2 by {
        close() using {
            1 < n;
        };
    }
}
```

```expect
fail: close() using` premise 0 is not exactly available
```
