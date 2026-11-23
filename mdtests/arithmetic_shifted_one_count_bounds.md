# Shifted-one divisors use established count bounds


```c filename=arithmetic.c
uint32 divide32(uint32 n, uint32 d) { return n / (1u << d); }
uint32 divide_narrowed(uint32 n, uint64 d) { return n / (1u << d); }
uint64 remain_widened(uint64 n, uint32 d) { return n % (1ULL << d); }
uint32 divide_signed_count(uint32 n, int32 d) { return n / (1u << d); }
```

```click
verifying "arithmetic.c";

uint32 divide32(uint32 n, uint32 d) { requires d <= 31u32; ensures true; }
uint32 divide_narrowed(uint32 n, uint64 d) { requires d < 32u64; ensures true; }
uint64 remain_widened(uint64 n, uint32 d) { requires d < 64u32; ensures true; }
uint32 divide_signed_count(uint32 n, int32 d) {
    requires 0 <= d;
    requires d < 32;
    ensures true;
}
```

```expect
pass
```
