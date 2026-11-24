# A signed certificate concludes a `uint32` order from intervals of known sign

Arithmetic search expands to ordinary proof steps, with the selected premises
stated explicitly in `close() using { ... }`.

```click
theorem allocation_range_fits(length: int32) {
    requires 0 <= length;
    requires length <= 536870911;
    ensures (length as uint32) <= 1073741823u32 by {
        close() using { 0 <= length; length <= 536870911; };
    }
}
```

```expect
pass
```
