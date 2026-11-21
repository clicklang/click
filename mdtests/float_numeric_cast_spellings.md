# Numeric float casts use the existing C conversions

```c filename=float_numeric_casts.c
float convert32(int32 x) { return (float)x; }
double widen(float x) { return (double)x; }
float narrow(double x) { return (float)x; }
```

```click
verifying "float_numeric_casts.c";

float convert32(int32 x) {
    requires x as float == x as float;
    ensures result == x as float;
}

double widen(float x) {
    requires x as double == x as double;
    ensures result == x as double;
}

float narrow(double x) {
    requires x as float == x as float;
    ensures result == x as float;
}

theorem numeric_cast_bits() {
    ensures 16777217 as float == float32_from_bits(0x4b800000) by { known(); }
    ensures 16777217 as double == float64_from_bits(0x4170000010000000) by { known(); }
    ensures float64_from_bits(0x3ff0000010000000) as float == float32_from_bits(0x3f800000) by { known(); }
    ensures float64_from_bits(0x3ff0000000000000) / (float32_from_bits(0x80000000) as double) == float64_from_bits(0xfff0000000000000) by { known(); }
    ensures isnan(float32_from_bits(0x7fc00123) as double) by { known(); }
}
```

```expect
pass
```
