# A positive nonwrapping offset of a masked word is a nonzero divisor

```c filename=arithmetic.c
uint32 divide(uint32 x, uint32 y) { return x / ((y & 7u) + 1u); }
uint64 remainder(uint64 x, uint64 y) { return x % (2ULL + (7ULL & y)); }
```

```click
verifying "arithmetic.c";

uint32 divide(uint32 x, uint32 y) { ensures true; }
uint64 remainder(uint64 x, uint64 y) { ensures true; }
```

```expect
pass
```
