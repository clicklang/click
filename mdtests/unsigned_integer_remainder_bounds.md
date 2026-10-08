# Unsigned remainder reduction bounds

A nonzero divisor bounds the unsigned remainder over the full u32 domain.
Strict order transfers to exact Integer observations without a signed cast.

```click
theorem native_reduction(value: uint32, divisor: uint32) {
    requires divisor != 0u32;
    ensures value % divisor < divisor by apply(uint32_remainder_less_than_divisor(value, divisor));
    ensures 0 <= to_integer(value % divisor) by apply(uint32_to_integer_bounds(value % divisor));
    ensures to_integer(value % divisor) < to_integer(divisor) by {
        apply(uint32_remainder_less_than_divisor(value, divisor));
        apply(uint32_less_than_to_integer(value % divisor, divisor));
    }
}
theorem adler_reduction(value: uint32) {
    ensures to_integer(value % 65521u32) <= 65520 by {
        apply(native_reduction(value, 65521u32));
        arithmetic() using { to_integer(value % 65521u32) < 65521; }
    }
}
theorem full_width_reduction() {
    ensures 4294967295u32 % 65521u32 == 224u32 by simp;
    ensures 2147483648u32 % 4294967295u32 == 2147483648u32 by simp;
    ensures 4294967295u32 % 1u32 == 0u32 by simp;
}
```

```expect
pass
```
