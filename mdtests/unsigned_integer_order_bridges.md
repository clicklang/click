# Unsigned Integer observation bridges

Unsigned order preserves the full u32 value, including the sign bit and
u32::MAX. The observation range follows from native unsigned order; it does
not distribute observations over wrapping addition.

```click
theorem preserve(left: uint32, right: uint32) {
    requires left <= right;
    ensures to_integer(left) <= to_integer(right) by {
        apply(uint32_less_equal_to_integer(left, right));
    }
}
theorem reflect(left: uint32, right: uint32) {
    requires to_integer(left) <= to_integer(right);
    ensures left <= right by {
        apply(uint32_less_equal_of_to_integer(left, right));
    }
}
theorem observed_range(value: uint32) {
    ensures 0 <= to_integer(value) by { apply(uint32_to_integer_bounds(value)); }
    ensures to_integer(value) <= 4294967295 by { apply(uint32_to_integer_bounds(value)); }
}
theorem full_width() {
    ensures to_integer(2147483648u32) == 2147483648 by simp;
    ensures to_integer(4294967295u32) == 4294967295 by simp;
    ensures to_integer(4294967295u32 + 1u32) == 0 by simp;
}
```

```expect
pass
```
