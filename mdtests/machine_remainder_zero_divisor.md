# An unsigned remainder needs a nonzero divisor

```click
theorem tail_bounds(n: uint64, size: uint64) {
    ensures n % size < size by { normalize(); }
}
```

```expect
fail: normalize
```
