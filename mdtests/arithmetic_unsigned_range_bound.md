# Signed allocation bounds establish unsigned byte-count bounds

A `uint32` order is checked from its operands' signed intervals, each read as
unsigned once its sign is known. Explicit signed bounds must suffice to check
the byte-count obligation, without search or an extra unsigned assumption.

```click
theorem allocation_range_fits(length: int32) {
    requires 0 <= length;
    requires length <= 536870911;
    ensures ((uint32)length) <= 1073741823u32 by {
        arithmetic() using {
            0 <= length;
            length <= 536870911;
        };
    }
}
```

```expect
pass
```
