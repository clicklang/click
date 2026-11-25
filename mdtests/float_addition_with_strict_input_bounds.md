# Strict bounds support replay for an addition followed by a cast

```c filename=strict.c
int32 cast_sum(double x, double y) {
    return (int32)(x + y);
}
```

```click
verifying "strict.c";

int32 cast_sum(double x, double y) {
    requires x > float64_from_bits(0xc024000000000000u64);
    requires x < float64_from_bits(0x4024000000000000u64);
    requires y > float64_from_bits(0xc000000000000000u64);
    requires y < float64_from_bits(0x4000000000000000u64);
    ensures true;
}
```

```expect
pass
```
