# Exact float bit literals preserve IEEE values

```click
theorem float_bits() {
    ensures float32_from_bits(0x3f800000u32) == float32_from_bits(0x3f800000) by { normalize(); }
    ensures iszero(float32_from_bits(0x80000000u32)) by { normalize(); }
    ensures iszero(float64_from_bits(0x8000000000000000u64)) by { normalize(); }
    ensures isinf(float32_from_bits(0x7f800000u32)) by { normalize(); }
    ensures isnan(float32_from_bits(0x7fc00123u32)) by { normalize(); }
    ensures isnan(float64_from_bits(0x7ff8000000000123u64)) by { normalize(); }
    ensures issubnormal(float64_from_bits(0x0000000000000001u64)) by { normalize(); }
}
```

```expect
pass
```
