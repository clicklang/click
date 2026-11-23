# Float bounds compose through successive rounded literal operations

```c filename=arithmetic.c
int32 scale_twice(float x) { return (int32)((x * 0.5f) * 0.5f); }
int32 double_twice(float x) { return (int32)((2.0f * x) * 2.0f); }
int32 divide_two(float x) { return (int32)(x / 2.0f); }
int32 add_one(float x) { return (int32)(x + 1.0f); }
```

```click
verifying "arithmetic.c";

int32 scale_twice(float x) {
    requires x >= float32_from_bits(0xc1200000);
    requires x <= float32_from_bits(0x41200000);
    ensures true;
}

int32 double_twice(float x) {
    requires x >= float32_from_bits(0xc1200000);
    requires x <= float32_from_bits(0x41200000);
    ensures true;
}

int32 divide_two(float x) {
    requires x >= float32_from_bits(0xc1200000);
    requires x <= float32_from_bits(0x41200000);
    ensures true;
}

theorem negative_divisor_bound(x: float) {
    requires x >= float32_from_bits(0xc1200000);
    ensures x / float32_from_bits(0xc0000000) <= float32_from_bits(0x40a00000) by {
        normalize() using { x >= float32_from_bits(0xc1200000); };
    }
}

int32 add_one(float x) {
    requires x >= float32_from_bits(0xc1200000);
    requires x <= float32_from_bits(0x41200000);
    ensures true;
}

theorem add_bound(x: float) {
    requires x >= float32_from_bits(0xc1200000);
    ensures x + float32_from_bits(0x3f800000) >= float32_from_bits(0xc1100000) by {
        normalize() using { x >= float32_from_bits(0xc1200000); };
    }
}
```

```expect
pass
```
