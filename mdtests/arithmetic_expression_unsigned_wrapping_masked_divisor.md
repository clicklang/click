# A masked sum can still wrap to zero

```c filename=arithmetic.c
uint32 divide(uint32 x, uint32 y) { return x / ((y & 0x80000000u) + 0x80000000u); }
```

```click
verifying "arithmetic.c";

uint32 divide(uint32 x, uint32 y) { ensures true; }
```

```expect
fail: nonzero divisor
```
