# IEEE sign negation reverses a bound before an integer cast

```c filename=negate.c
int32 cast32(float x) { return (int32)-x; }
int32 cast64(double x) { return (int32)-x; }
```

```click
verifying "negate.c";

int32 cast32(float x) {
    requires x >= float32_from_bits(0);
    requires x <= float32_from_bits(0x3f800000);
    ensures true;
}

int32 cast64(double x) {
    requires x >= float64_from_bits(0);
    requires x <= float64_from_bits(0x3ff0000000000000);
    ensures true;
}

theorem negated_lower_bound(x: float) {
    requires x <= float32_from_bits(0x3f800000);
    ensures -x >= float32_from_bits(0xbf800000) by known();
}

theorem negated_strict_upper_bound(x: double) {
    requires float64_from_bits(0xbff0000000000000) < x;
    ensures -x < float64_from_bits(0x3ff0000000000000) by known();
}

theorem ordered_negated_literal() {
    ensures -float32_from_bits(0x3f800000) < float32_from_bits(0) by { known(); }
}
```

```expect
pass
```
