# Subtracting with a finite literal at floating-point infinity

```c filename=subtract.c
double subtract_at_infinity(double x) {
    return x - 1.0;
}
```

```click
verifying "subtract.c";

double subtract_at_infinity(double x) {
    requires x >= float64_from_bits(0x7ff0000000000000u64);
    ensures result >= float64_from_bits(0x7ff0000000000000u64);
}

theorem positive_right(x: float) {
    requires x >= float32_from_bits(0x7f800000);
    ensures x - float32_from_bits(0x3f800000)
        >= float32_from_bits(0x7f800000) by close();
}

theorem negative_left(x: float) {
    requires x <= float32_from_bits(0xff800000);
    ensures float32_from_bits(0x3f800000) - x
        >= float32_from_bits(0x7f800000) by close();
}

theorem positive_left(x: double) {
    requires x >= float64_from_bits(0x7ff0000000000000u64);
    ensures float64_from_bits(0xbff0000000000000u64) - x
        <= float64_from_bits(0xfff0000000000000u64) by close();
}

theorem negative_right(x: double) {
    requires x <= float64_from_bits(0xfff0000000000000u64);
    ensures x - float64_from_bits(0x3ff0000000000000u64)
        <= float64_from_bits(0xfff0000000000000u64) by close();
}
```

```expect
pass
```
