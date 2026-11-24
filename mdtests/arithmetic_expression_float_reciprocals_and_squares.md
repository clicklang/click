# Floating-point casts use reciprocal and square bounds

```c filename=arithmetic.c
int32 reciprocal_negative(float x) { return (int32)(1.0f / x); }
int32 negative_reciprocal(double x) { return (int32)(-1.0 / x); }
int32 reciprocal_strict(float x) { return (int32)(1.40129846e-45f / x); }
uint32 square(float x) { return (uint32)(x * x); }
```

```click
verifying "arithmetic.c";

int32 reciprocal_negative(float x) {
    requires x <= float32_from_bits(0xbf800000);
    ensures true;
}
int32 negative_reciprocal(double x) {
    requires x >= float64_from_bits(0x3ff0000000000000u64);
    ensures true;
}
int32 reciprocal_strict(float x) {
    requires x > float32_from_bits(0x80000000);
    ensures true;
}
uint32 square(float x) {
    requires x >= float32_from_bits(0xc0000000);
    requires x <= float32_from_bits(0x40000000);
    ensures true;
}
```

```expect
pass
```
