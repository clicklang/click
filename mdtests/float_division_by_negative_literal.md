# Float quotient order with a negative literal divisor

```c filename=negative_divisor.c
int32 divide_negative_two(float x) { return (int32)(x / -2.0f); }
```

```click
verifying "negative_divisor.c";

int32 divide_negative_two(float x) {
    requires x >= float32_from_bits(0xc1200000);
    requires x <= float32_from_bits(0x41200000);
    ensures true;
}

theorem division_lower(x: float, bound: float) {
    requires x <= bound;
    ensures x / float32_from_bits(0xc0000000) >= bound / float32_from_bits(0xc0000000) by {
        apply(click::float_order::float32_divide_negative_lower(float32_from_bits(0xc0000000), x, bound));
        close();
    }
}

theorem division_upper(x: float, bound: float) {
    requires x >= bound;
    ensures x / float32_from_bits(0xc0000000) <= bound / float32_from_bits(0xc0000000) by {
        apply(click::float_order::float32_divide_negative_upper(float32_from_bits(0xc0000000), x, bound));
        close();
    }
}
```

```expect
pass
```
