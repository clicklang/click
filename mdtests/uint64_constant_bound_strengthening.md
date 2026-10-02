# Full-width unsigned bounds

Unsigned bounds retain their meaning beyond the signed sign bit. The negated
outer branch must rule out the inner small-range branch using its own fact.

```c filename=uint64_constant_bound_strengthening.c
uint32 classify(uint64 n) {
    if (n <= 65535ULL) return 0U;
    if (n < 253ULL) return 1U;
    return 2U;
}
uint64 quotient(uint64 n, uint64 d) { return n / d; }
```

```click
verifying "uint64_constant_bound_strengthening.c";
uint32 classify(uint64 n) {
    ensures result != 1u32;
} by { execute(); simp(); }
uint64 quotient(uint64 n, uint64 d) {
    requires d > 0u64;
    ensures result == n / d;
} by { execute(); simp(); }
```

```expect
pass
```
