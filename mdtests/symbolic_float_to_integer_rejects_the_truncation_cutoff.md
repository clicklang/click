# An unsigned cast cannot truncate minus one to a representable value

```c filename=cast.c
uint32 convert(double x) { return (uint32)x; }
```

```click
verifying "cast.c";

uint32 convert(double x) {
    requires isfinite(x);
    requires x == float64_from_bits(0xbff0000000000000u64);
    requires x < float64_from_bits(0x41f0000000000000u64);
    ensures true;
}
```

```expect
fail: x > float64_from_bits(0xbff0000000000000u64)
```
