# Fixed right shifts bound promoted unsigned counts


```c filename=arithmetic.c
uint32 shift32(uint32 x, uint8 d) { return x << (d >> 3); }
uint64 shift64(uint64 x, uint16 d) { return x << (d >> 10); }
```

```click
verifying "arithmetic.c";

uint32 shift32(uint32 x, uint8 d) { ensures true; }
uint64 shift64(uint64 x, uint16 d) { ensures true; }
```

```expect
pass
```
