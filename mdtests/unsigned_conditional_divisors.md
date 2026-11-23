# A conditional divisor uses its own nonzero guard

```c filename=divide.c
uint32 divide32(uint32 n, uint32 d) { return n / (d ? d : 1u); }
uint64 divide64(uint64 n, uint64 d) { return n / (d != 0ULL ? d : 1ULL); }
uint32 remain32(uint32 n, uint32 d) { return n % (0u != d ? d : 1u); }
uint64 remain64(uint64 n, uint64 d) { return n % (d ? d : 1ULL); }
```

```click
verifying "divide.c";

uint32 divide32(uint32 n, uint32 d) { ensures true; }
uint64 divide64(uint64 n, uint64 d) { ensures true; }
uint32 remain32(uint32 n, uint32 d) { ensures true; }
uint64 remain64(uint64 n, uint64 d) { ensures true; } by {
    step() by { known(); }
    known();
}
```

```expect
pass
```
