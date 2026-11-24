# Float casts retain the rounded endpoints of integer bounds

```c filename=arithmetic.c
int32 via_double(int32 x) { return (int32)(double)x; }
uint32 unsigned_via_double(uint32 x) { return (uint32)(double)x; }
uint16 short_via_float(uint16 x) { return (uint16)(float)x; }
int32 via_float(int32 x) { return (int32)(float)x; }
```

```click
verifying "arithmetic.c";

int32 via_double(int32 x) { ensures true; }
uint32 unsigned_via_double(uint32 x) { ensures true; }
uint16 short_via_float(uint16 x) { ensures true; }
int32 via_float(int32 x) { requires x < 2147483584; ensures true; }

theorem rounded_upper(x: int32) {
    requires x <= 2147483583;
    ensures x as float <= float32_from_bits(0x4effffff) by {
        normalize() using { x <= 2147483583; };
    }
}
```

```expect
pass
```
