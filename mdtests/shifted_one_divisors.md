# An in-range shift of one is a nonzero divisor

```c filename=divide.c
uint32 divide32(uint32 n, uint32 d) { return n / (1u << d); }
uint64 divide64(uint64 n, uint64 d) { return n / (1ULL << d); }
uint32 remain32(uint32 n, uint32 d) { return n % (1u << d); }
uint64 remain64(uint64 n, uint64 d) { return n % (1ULL << d); }
```

```click
verifying "divide.c";

uint32 divide32(uint32 n, uint32 d) { requires d < 32u32; ensures true; } by {
    have (1u32 << d) != 0u32 by {
        apply(shifted_one32(d));
    }
    step();
}
uint64 divide64(uint64 n, uint64 d) { requires d < 64u64; ensures true; } by {
    have (1u64 << d) != 0u64 by {
        apply(shifted_one64(d));
    }
    step();
}
uint32 remain32(uint32 n, uint32 d) { requires d < 32u32; ensures true; } by {
    have (1u32 << d) != 0u32 by {
        apply(shifted_one32(d));
    }
    step();
}
uint64 remain64(uint64 n, uint64 d) { requires d < 64u64; ensures true; } by {
    have (1u64 << d) != 0u64 by {
        apply(shifted_one64(d));
    }
    step();
}

theorem shifted_one32(d: uint32) {
    requires d < 32u32;
    ensures (1u32 << d) != 0u32 by known();
}

theorem shifted_one64(d: uint64) {
    requires d < 64u64;
    ensures (1u64 << d) != 0u64 by known();
}
```

```expect
pass
```
