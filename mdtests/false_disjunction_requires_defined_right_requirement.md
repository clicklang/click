# A false left disjunct cannot hide division by zero on the right

The right side of `or` is read only where the left side is false. Here that
is `x == 0`, where `5u32 / x` has no value, so the requirement is refused
where it is declared.

```click
theorem guarded(x: uint32) {
    requires x != 0u32 or 5u32 / x == 1u32;
    ensures 1 == 1 by solve();
}

theorem invalid_zero_instance() {
    ensures 1 == 1 by apply(guarded(0u32));
}
```

```expect
fail: not established: `x != 0 or x != 0`
```
