# Rounded multiplication by a negative float literal

```c filename=multiplication.c
int32 multiply_left(float x) { return (int32)(-2.0f * x); }
int32 multiply_right(float x) { return (int32)(x * -2.0f); }
```

```click
verifying "multiplication.c";

int32 multiply_left(float x) {
    requires x >= float32_from_bits(0xc1200000);
    requires x <= float32_from_bits(0x41200000);
    ensures true;
}

int32 multiply_right(float x) {
    requires x >= float32_from_bits(0xc1200000);
    requires x <= float32_from_bits(0x41200000);
    ensures true;
}

theorem negative_product(x: float) {
    requires x >= float32_from_bits(0xc1200000);
    ensures x * float32_from_bits(0xc0000000) <= float32_from_bits(0x41a00000) by close();
}

theorem lower(x: float, bound: float) {
    requires x <= bound;
    ensures float32_from_bits(0xc0000000) * x >= float32_from_bits(0xc0000000) * bound by {
        apply(click::float_order::float32_scale_negative_lower(float32_from_bits(0xc0000000), x, bound));
    }
}

theorem upper(x: float, bound: float) {
    requires x >= bound;
    ensures float32_from_bits(0xc0000000) * x <= float32_from_bits(0xc0000000) * bound by {
        apply(click::float_order::float32_scale_negative_upper(float32_from_bits(0xc0000000), x, bound));
    }
}

theorem right_lower(x: float, bound: float) {
    requires x <= bound;
    ensures x * float32_from_bits(0xc0000000) >= bound * float32_from_bits(0xc0000000) by {
        apply(click::float_order::float32_scale_negative_right_lower(float32_from_bits(0xc0000000), x, bound));
    }
}

theorem right_upper(x: float, bound: float) {
    requires x >= bound;
    ensures x * float32_from_bits(0xc0000000) <= bound * float32_from_bits(0xc0000000) by {
        apply(click::float_order::float32_scale_negative_right_upper(float32_from_bits(0xc0000000), x, bound));
    }
}
```

```expect
pass
```
