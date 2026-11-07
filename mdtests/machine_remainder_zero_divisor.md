# An unsigned remainder needs a nonzero divisor

A specification remainder by a divisor that may be zero is defined: at zero
it is the opaque total remainder, which is not below the divisor. So
`n % size < size` does not normalize without a nonzero `size`.

```click
theorem tail_bounds(n: uint64, size: uint64) {
    ensures n % size < size by normalize();
}
```

```expect
fail: `normalize` goal did not normalize to true
```
