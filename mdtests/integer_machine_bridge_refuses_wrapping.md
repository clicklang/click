# A machine bridge refuses bounds outside its format

The exact result is 2^64, while unsigned machine addition wraps to zero.
The two stated Integer bounds cannot authorize that bridge.

```click
theorem wraps(x: uint64) {
    requires x == 18446744073709551615u64;
    requires 0 <= to_integer(x) + 1;
    requires to_integer(x) + 1 <= 18446744073709551616;
    ensures to_integer(x + 1u64) == to_integer(x) + 1 by {
        close() using {
            0 <= to_integer(x) + 1;
            to_integer(x) + 1 <= 18446744073709551616;
        };
    }
}
```

```expect
fail: `close() using` could not prove the current goal from only its listed premises
```
