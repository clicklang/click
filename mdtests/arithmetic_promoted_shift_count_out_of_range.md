# Promotion still allows out-of-range shift counts


```c filename=arithmetic.c
uint32 shift(uint32 x, uint8 d) { return x << (d >> 2); }
```

```click
verifying "arithmetic.c";

uint32 shift(uint32 x, uint8 d) { ensures true; }
```

```expect
fail: invalid shift
```
