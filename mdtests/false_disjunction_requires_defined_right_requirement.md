# A false left disjunct cannot hide division by zero on the right

```click
theorem guarded(x: uint32) {
    requires x != 0u32 or 5u32 / x == 1u32;
    ensures 1 == 1 by simp;
}

theorem invalid_zero_instance() {
    ensures 1 == 1 by apply(guarded(0u32));
}
```

```expect
fail: proof step
```
