# A uint32 predecessor at zero is refused

`to_integer(x - 1u32) < to_integer(x)` is false at `x == 0`, where the
predecessor wraps to `UINT_MAX`. Without the fact `0u32 < x`, the omitted proof cannot
prove it.

```click
theorem predecessor_without_a_guard(x: uint32) {
    ensures to_integer(x - 1u32) < to_integer(x);
}
```

```expect
fail: could not establish `to_integer((x - 1u32)) < to_integer(x)`
```
