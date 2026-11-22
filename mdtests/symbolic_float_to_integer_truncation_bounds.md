# Symbolic float-to-integer casts check the range after truncation

Negative fractions above `-1` truncate to zero. Signed casts can also
accept fractions immediately below the destination minimum when the source
format can represent them. When the source format has no float between
the minimum minus one and the minimum, the minimum itself is allowed.

```c filename=cast.c
uint32 to_unsigned(double x) { return (uint32)x; }
int32 to_signed(double x) { return (int32)x; }
short to_short(float x) { return (short)x; }
int32 from_float(float x) { return (int32)x; }
long to_long(double x) { return (long)x; }
```

```click
verifying "cast.c";

uint32 to_unsigned(double x) {
    requires x > float64_from_bits(0xbff0000000000000u64);
    requires x < float64_from_bits(0x0000000000000000u64);
    requires x < float64_from_bits(0x41f0000000000000u64);
    ensures true;
}

int32 to_signed(double x) {
    requires x > float64_from_bits(0xc1e0000000200000u64);
    requires x < float64_from_bits(0xc1e0000000000000u64);
    requires x < float64_from_bits(0x41e0000000000000u64);
    ensures true;
}

int16 to_short(float x) {
    requires x > float32_from_bits(0xc7000100u32);
    requires x < float32_from_bits(0xc7000000);
    requires x < float32_from_bits(0x47000000u32);
    ensures true;
}

int32 from_float(float x) {
    requires x >= float32_from_bits(0xcf000000);
    requires x < float32_from_bits(0x4f000000);
    ensures true;
}

int64 to_long(double x) {
    requires x >= float64_from_bits(0xc3e0000000000000u64);
    requires x < float64_from_bits(0x43e0000000000000u64);
    ensures true;
}
```

```expect
pass
```
