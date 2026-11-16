# Unsigned widening retains a certificate's exact conclusion

Arithmetic search expands to ordinary proof steps, with the selected premises
stated explicitly in `solve() using { ... }`.

```click
import click::integer;
theorem positive_is_nonzero(x: int32) {
    requires 1 <= to_integer(x as uint32 as uint64);
    ensures not (to_integer(x as uint32 as uint64) == 0) by {
        solve() using { 1 <= to_integer(x as uint32 as uint64); };
    }
}
theorem widened_positive_is_unequal_to_zero(x: int32) {
    requires 1 <= to_integer(x as uint32 as uint64);
    ensures to_integer(x as uint32 as uint64) != 0 by {
        solve() using { 1 <= to_integer(x as uint32 as uint64); };
    }
}
```

```expect
pass
```
