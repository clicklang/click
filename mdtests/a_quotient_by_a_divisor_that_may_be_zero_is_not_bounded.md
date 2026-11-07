# A quotient by a divisor that may be zero is not bounded by its dividend

`a / b <= a` holds for every nonzero `b`, but at `b == 0` the quotient is the
opaque value, which bounds nothing.

```click
theorem quotient_bound(a: uint32, b: uint32) {
    ensures a / b <= a;
}
```

```expect
fail: could not establish `(a / b) <= a`
```
