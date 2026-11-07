# A quotient by zero is not zero

`x / 0u32` is the opaque total quotient, not a chosen value: nothing says it
is zero.

```click
theorem quotient_by_zero(x: uint32) {
    ensures x / 0u32 == 0u32;
}
```

```expect
fail: could not establish `(x / 0u32) == 0u32`
```
