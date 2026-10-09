# An int64 sum that may overflow is not arithmetic

`i <= length` bounds `i` from above only. `i - 1` may then go below the
least `int64`, where the subtraction is undefined, so it has no Integer
observation to reason with. The step is refused, naming the difference and
the bound it could not show.

`arithmetic_proves_int64_order_goals.md` has the goals that do follow.

```click
theorem predecessor(i: int64, length: int64) {
    requires i <= length;
    ensures i - 1i64 <= length by {
        arithmetic() using { i <= length; }
    }
}
```

```expect
fail: stays within int64
```
