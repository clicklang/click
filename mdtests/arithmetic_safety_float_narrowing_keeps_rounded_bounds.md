# Narrowing carries the rounded operand bounds into an integer cast

```c filename=arithmetic.c
int32 cast_narrowed(double x) { return (int32)(float)x; }
```

```click
verifying "arithmetic.c";

int32 cast_narrowed(double x) {
    requires x >= float64_from_bits(0xbff0000000000000u64);
    requires x <= float64_from_bits(0x3ff0000000000000u64);
    ensures true;
}

theorem rounded(x: double) {
    requires x < float64_from_bits(0x3ff0000000000000u64);
    ensures x as float <= float32_from_bits(0x3f800000) by {
        normalize() using { x < float64_from_bits(0x3ff0000000000000u64); };
    }
}
```

```expect
pass
```
