# Float inequality keeps its polarity in propositions and Boolean values

```click
function different32(x: float, y: float) -> Bool { if x != y { true } else { false } }
function different64(x: double, y: double) -> Bool { if x != y { true } else { false } }

theorem float_inequality() {
    ensures float32_from_bits(0x3f800000) != float32_from_bits(0x40000000) by { known(); }
    ensures float64_from_bits(0x3ff0000000000000) != float64_from_bits(0x4000000000000000) by { known(); }
    ensures different32(float32_from_bits(0x3f800000), float32_from_bits(0x40000000)) by { unfold(different32(float32_from_bits(0x3f800000), float32_from_bits(0x40000000))); known(); }
    ensures different64(float64_from_bits(0x3ff0000000000000), float64_from_bits(0x4000000000000000)) by { unfold(different64(float64_from_bits(0x3ff0000000000000), float64_from_bits(0x4000000000000000))); known(); }
    ensures not different32(float32_from_bits(0), float32_from_bits(0x80000000)) by { unfold(different32(float32_from_bits(0), float32_from_bits(0x80000000))); known(); }
    ensures not different64(float64_from_bits(0), float64_from_bits(0x8000000000000000)) by { unfold(different64(float64_from_bits(0), float64_from_bits(0x8000000000000000))); known(); }
    ensures different32(float32_from_bits(0x7fc00123), float32_from_bits(0x7fc00123)) by { unfold(different32(float32_from_bits(0x7fc00123), float32_from_bits(0x7fc00123))); known(); }
    ensures different64(float64_from_bits(0x7ff8000000000123), float64_from_bits(0x7ff8000000000123)) by { unfold(different64(float64_from_bits(0x7ff8000000000123), float64_from_bits(0x7ff8000000000123))); known(); }
}
```

```expect
pass
```
