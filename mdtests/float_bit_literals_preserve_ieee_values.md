# Exact float bit literals preserve IEEE values

```click
theorem float_bits() {
    ensures float32_from_bits(0x3f800000u32) == float32_from_bits(0x3f800000) by { close(); }
    ensures float32_from_bits(0x80000000u32) == float32_from_bits(0u32) by { close(); }
    ensures float64_from_bits(0x7ff8000000000123u64) != float64_from_bits(0x7ff8000000000123u64) by { close(); }
    ensures not (float64_from_bits(0x7ff8000000000123u64) <= float64_from_bits(0u64)) by { close(); }
    ensures float32_from_bits(0xbf800000u32) < float32_from_bits(0x3f800000u32) by { close(); }
    ensures (if float32_from_bits(0x80000000u32) == float32_from_bits(0u32) { true } else { false }) == true by { close(); }
    ensures iszero(float32_from_bits(0x80000000u32)) by { close(); }
    ensures iszero(float64_from_bits(0x8000000000000000u64)) by { close(); }
    ensures isinf(float32_from_bits(0x7f800000u32)) by { close(); }
    ensures isnan(float32_from_bits(0x7fc00123u32)) by { close(); }
    ensures isnan(float64_from_bits(0x7ff8000000000123u64)) by { close(); }
    ensures issubnormal(float64_from_bits(0x0000000000000001u64)) by { close(); }
}
```

```expect
pass
```
