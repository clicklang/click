# Rounded multiplication by a finite double literal

```c filename=multiplication.c
int32 positive_left(double x) { return (int32)(2.0 * x); }
int32 positive_right(double x) { return (int32)(x * 2.0); }
int32 negative_left(double x) { return (int32)(-2.0 * x); }
int32 negative_right(double x) { return (int32)(x * -2.0); }
```

```click
verifying "multiplication.c";

int32 positive_left(double x) {
    requires x >= float64_from_bits(0xc024000000000000u64);
    requires x <= float64_from_bits(0x4024000000000000u64);
    ensures true;
}

int32 positive_right(double x) {
    requires x >= float64_from_bits(0xc024000000000000u64);
    requires x <= float64_from_bits(0x4024000000000000u64);
    ensures true;
}

int32 negative_left(double x) {
    requires x >= float64_from_bits(0xc024000000000000u64);
    requires x <= float64_from_bits(0x4024000000000000u64);
    ensures true;
}

int32 negative_right(double x) {
    requires x >= float64_from_bits(0xc024000000000000u64);
    requires x <= float64_from_bits(0x4024000000000000u64);
    ensures true;
}

theorem double_product(x: double) {
    requires x <= float64_from_bits(0x4024000000000000u64);
    ensures x * float64_from_bits(0x4000000000000000u64)
        <= float64_from_bits(0x4034000000000000u64) by close();
}

theorem lower(x: double, bound: double) {
    requires x >= bound;
    ensures float64_from_bits(0x4000000000000000u64) * x >= float64_from_bits(0x4000000000000000u64) * bound by {
        apply(click::float_order::float64_scale_lower(float64_from_bits(0x4000000000000000u64), x, bound));
    }
}

theorem upper(x: double, bound: double) {
    requires x <= bound;
    ensures float64_from_bits(0x4000000000000000u64) * x <= float64_from_bits(0x4000000000000000u64) * bound by {
        apply(click::float_order::float64_scale_upper(float64_from_bits(0x4000000000000000u64), x, bound));
    }
}

theorem right_lower(x: double, bound: double) {
    requires x >= bound;
    ensures x * float64_from_bits(0x4000000000000000u64) >= bound * float64_from_bits(0x4000000000000000u64) by {
        apply(click::float_order::float64_scale_right_lower(float64_from_bits(0x4000000000000000u64), x, bound));
    }
}

theorem right_upper(x: double, bound: double) {
    requires x <= bound;
    ensures x * float64_from_bits(0x4000000000000000u64) <= bound * float64_from_bits(0x4000000000000000u64) by {
        apply(click::float_order::float64_scale_right_upper(float64_from_bits(0x4000000000000000u64), x, bound));
    }
}

theorem negative_lower(x: double, bound: double) {
    requires x <= bound;
    ensures float64_from_bits(0xc000000000000000u64) * x >= float64_from_bits(0xc000000000000000u64) * bound by {
        apply(click::float_order::float64_scale_negative_lower(float64_from_bits(0xc000000000000000u64), x, bound));
    }
}

theorem negative_upper(x: double, bound: double) {
    requires x >= bound;
    ensures float64_from_bits(0xc000000000000000u64) * x <= float64_from_bits(0xc000000000000000u64) * bound by {
        apply(click::float_order::float64_scale_negative_upper(float64_from_bits(0xc000000000000000u64), x, bound));
    }
}

theorem negative_right_lower(x: double, bound: double) {
    requires x <= bound;
    ensures x * float64_from_bits(0xc000000000000000u64) >= bound * float64_from_bits(0xc000000000000000u64) by {
        apply(click::float_order::float64_scale_negative_right_lower(float64_from_bits(0xc000000000000000u64), x, bound));
    }
}

theorem negative_right_upper(x: double, bound: double) {
    requires x >= bound;
    ensures x * float64_from_bits(0xc000000000000000u64) <= bound * float64_from_bits(0xc000000000000000u64) by {
        apply(click::float_order::float64_scale_negative_right_upper(float64_from_bits(0xc000000000000000u64), x, bound));
    }
}
```

```expect
pass
```
