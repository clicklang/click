# An unsigned interval comparison of unknown sign is refused

Arithmetic search expands to ordinary proof steps, with the selected premises
stated explicitly in `close() using { ... }`.

```click
theorem allocation_range_fits(length: int32) {
    requires length <= 536870911;
    ensures (length as uint32) <= 1073741823u32 by {
        close() using { length <= 536870911; };
    }
}
```

```expect
fail: solve
```
