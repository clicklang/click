# Floating-point finiteness from ordered bounds

```c filename=finite.c
double finite_identity(double x) {
    return x;
}
```

```click
verifying "finite.c";

double finite_identity(double x) {
    requires x > float64_from_bits(0xfff0000000000000u64);
    requires x < float64_from_bits(0x7ff0000000000000u64);
    ensures isfinite(result);
}

theorem finite_between(x: float) {
    requires x > float32_from_bits(0xbf800000);
    requires x < float32_from_bits(0x3f800000);
    ensures isfinite(x) by close();
}

theorem strict_infinities(x: double) {
    requires x > float64_from_bits(0xfff0000000000000u64);
    requires x < float64_from_bits(0x7ff0000000000000u64);
    ensures isfinite(x) by close();
}

theorem inclusive_bounds(x: float) {
    requires x >= float32_from_bits(0xff7fffff);
    requires x <= float32_from_bits(0x7f7fffff);
    ensures isfinite(x) by close();
}

theorem finite_negated(x: double) {
    requires x > float64_from_bits(0xfff0000000000000u64);
    requires x < float64_from_bits(0x7ff0000000000000u64);
    ensures isfinite(-x) by close();
}

theorem finite_widened(x: float) {
    requires x > float32_from_bits(0xbf800000);
    requires x < float32_from_bits(0x3f800000);
    ensures isfinite(x as double) by close();
}
theorem zero_product_with_ordered_operand(x: double) {
    requires x > float64_from_bits(0xfff0000000000000u64);
    requires x < float64_from_bits(0x7ff0000000000000u64);
    ensures x * float64_from_bits(0u64) >= float64_from_bits(0u64) by close();
}

```

```expect
pass
```
