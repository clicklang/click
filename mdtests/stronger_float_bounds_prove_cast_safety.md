# Stronger float bounds prove a cast safe

```c filename=cast.c
int32 cast(double x) { return (int32)x; }
int32 cast_saved(double x) {
    double saved = x;
    x = -1.0;
    return (int32)saved;
}
```

```click
verifying "cast.c";

int32 cast(double x) {
    requires x > float64_from_bits(0);
    requires x <= float64_from_bits(0x3ff0000000000000);
    ensures true;
}

int32 cast_saved(double x) {
    requires x > float64_from_bits(0);
    requires x <= float64_from_bits(0x3ff0000000000000);
    ensures true;
}

theorem weaken_float32_bound(x: float) {
    requires float32_from_bits(0x3f800000) >= x;
    ensures x < float32_from_bits(0x40000000) by { close(); }
}

theorem cite_float32_bound(x: float) {
    requires x > float32_from_bits(0x80000000);
    ensures x >= float32_from_bits(0) by {
        normalize() using { x > float32_from_bits(0x80000000); };
    }
}
```

```expect
pass
```
