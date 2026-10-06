# Strict order of observed native values

```click
theorem derived_strict_observer(left: int32, right: int32) {
    requires left < right;
    ensures to_integer(left) < to_integer(right) by {
        if to_integer(right) <= to_integer(left) {
            apply(int32_less_equal_of_to_integer(right, left));
            contradiction(left < right);
        } else {
            arithmetic() using { not (to_integer(right) <= to_integer(left)); }
        }
    }
}
theorem strict_observer(left: int32, right: int32) {
    requires left < right;
    ensures to_integer(left) < to_integer(right) by {
        apply(int32_less_than_to_integer(left, right));
    }
}
```

```expect
pass
```
