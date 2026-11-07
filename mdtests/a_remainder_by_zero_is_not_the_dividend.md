# A remainder by zero is not the dividend

`x % 0u64` is the opaque total remainder, not a chosen value: nothing says it
equals `x`, or is at most `x`.

```click
theorem remainder_by_zero(x: uint64) {
    ensures x % 0u64 <= x;
}
```

```expect
fail: could not establish `(x % 0u64) <= x`
```
