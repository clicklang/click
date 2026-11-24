# Exact float widening preserves ordered bounds

```c filename=cast.c
int32 convert(float x) { return (int32)(double)x; }
```

```click
verifying "cast.c";

int32 convert(float x) {
    requires x >= float32_from_bits(0);
    requires x <= float32_from_bits(0x3f800000);
    ensures true;
}

theorem strict_bound(x: float) {
    requires float32_from_bits(0x3f800000) > x;
    ensures x as double < float64_from_bits(0x3ff0000000000000) by known();
}
```

```expect
pass
```
