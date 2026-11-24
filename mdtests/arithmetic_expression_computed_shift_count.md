# A fixed right shift supplies a bound on a computed divisor count

```c filename=arithmetic.c
uint32 divide(uint32 n, uint32 d) { return n / (1u << (d >> 27u)); }
```

```click
verifying "arithmetic.c";

uint32 divide(uint32 n, uint32 d) { ensures true; }
```

```expect
pass
```
