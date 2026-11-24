# Reciprocals and one-sided signed divisor ranges bound float casts

```c filename=arithmetic.c
int32 reciprocal64(double y) { return (int32)(1.0 / y); }
int32 divide_negative_denominator(double x, double y) { return (int32)(x / y); }
```

```click
verifying "arithmetic.c";

int32 reciprocal64(double y) {
    requires float64_from_bits(0x3ff0000000000000u64) < y;
    ensures true;
}

int32 divide_negative_denominator(double x, double y) {
    requires x >= float64_from_bits(0xc000000000000000u64);
    requires x <= float64_from_bits(0x4008000000000000u64);
    requires y >= float64_from_bits(0xc010000000000000u64);
    requires y <= float64_from_bits(0xbff0000000000000u64);
    ensures true;
}
```

```expect
pass
```
