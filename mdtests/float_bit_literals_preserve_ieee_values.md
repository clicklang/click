# Exact float bit literals preserve IEEE values

```click
theorem float_bits() {
    ensures float32_from_bits(0x3f800000u32) == float32_from_bits(0x3f800000) by { known(); }
    ensures float32_from_bits(0x80000000u32) == float32_from_bits(0u32) by { known(); }
    ensures float64_from_bits(0x7ff8000000000123u64) != float64_from_bits(0x7ff8000000000123u64) by { known(); }
    ensures not (float64_from_bits(0x7ff8000000000123u64) <= float64_from_bits(0u64)) by { known(); }
    ensures float32_from_bits(0xbf800000u32) < float32_from_bits(0x3f800000u32) by { known(); }
    ensures (if float32_from_bits(0x80000000u32) == float32_from_bits(0u32) { true } else { false }) == true by { known(); }
    ensures iszero(float32_from_bits(0x80000000u32)) by { known(); }
    ensures iszero(float64_from_bits(0x8000000000000000u64)) by { known(); }
    ensures isinf(float32_from_bits(0x7f800000u32)) by { known(); }
    ensures isnan(float32_from_bits(0x7fc00123u32)) by { known(); }
    ensures isnan(float64_from_bits(0x7ff8000000000123u64)) by { known(); }
    ensures issubnormal(float64_from_bits(0x0000000000000001u64)) by { known(); }
}
```

```expect
pass
```
