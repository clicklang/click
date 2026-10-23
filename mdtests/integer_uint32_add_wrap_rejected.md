# Defined unsigned addition does not imply a non-wrapping observation

```click
theorem invalid_unsigned_sum(a: uint32, b: uint32) {
    requires defined(a + b);
    ensures to_integer(a + b) == to_integer(a) + to_integer(b) by auto();
}
```

```expect
fail: proof step
```
