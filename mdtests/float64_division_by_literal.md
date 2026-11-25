# Rounded double division by a finite literal

```c filename=division.c
int32 divide_positive(double x) { return (int32)(x / 2.0); }
int32 divide_negative(double x) { return (int32)(x / -2.0); }
```

```click
verifying "division.c";

int32 divide_positive(double x) {
    requires x >= float64_from_bits(0xc024000000000000u64);
    requires x <= float64_from_bits(0x4024000000000000u64);
    ensures true;
}

int32 divide_negative(double x) {
    requires x >= float64_from_bits(0xc024000000000000u64);
    requires x <= float64_from_bits(0x4024000000000000u64);
    ensures true;
}

theorem double_divisor_bound(x: double) {
    requires x >= float64_from_bits(0xc024000000000000u64);
    ensures x / float64_from_bits(0xc000000000000000u64)
        <= float64_from_bits(0x4014000000000000u64) by close();
}

theorem positive_lower(x: double, bound: double) {
    requires x >= bound;
    ensures x / float64_from_bits(0x4000000000000000u64) >= bound / float64_from_bits(0x4000000000000000u64) by {
        apply(click::float_order::float64_divide_positive_lower(float64_from_bits(0x4000000000000000u64), x, bound));
    }
}

theorem positive_upper(x: double, bound: double) {
    requires x <= bound;
    ensures x / float64_from_bits(0x4000000000000000u64) <= bound / float64_from_bits(0x4000000000000000u64) by {
        apply(click::float_order::float64_divide_positive_upper(float64_from_bits(0x4000000000000000u64), x, bound));
    }
}

theorem negative_lower(x: double, bound: double) {
    requires x <= bound;
    ensures x / float64_from_bits(0xc000000000000000u64) >= bound / float64_from_bits(0xc000000000000000u64) by {
        apply(click::float_order::float64_divide_negative_lower(float64_from_bits(0xc000000000000000u64), x, bound));
    }
}

theorem negative_upper(x: double, bound: double) {
    requires x >= bound;
    ensures x / float64_from_bits(0xc000000000000000u64) <= bound / float64_from_bits(0xc000000000000000u64) by {
        apply(click::float_order::float64_divide_negative_upper(float64_from_bits(0xc000000000000000u64), x, bound));
    }
}
```

```expect
pass
```
