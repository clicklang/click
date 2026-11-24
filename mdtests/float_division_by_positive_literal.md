# Float quotient order with a positive literal divisor

```click
theorem division_lower(x: float, bound: float) {
    requires x >= bound;
    ensures x / float32_from_bits(0x40000000) >= bound / float32_from_bits(0x40000000) by {
        apply(click::float_order::float32_divide_positive_lower(float32_from_bits(0x40000000), x, bound));
        close();
    }
}

theorem division_upper(x: float, bound: float) {
    requires x <= bound;
    ensures x / float32_from_bits(0x40000000) <= bound / float32_from_bits(0x40000000) by {
        apply(click::float_order::float32_divide_positive_upper(float32_from_bits(0x40000000), x, bound));
        close();
    }
}
```

```expect
pass
```
