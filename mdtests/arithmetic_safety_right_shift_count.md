# A fixed right shift bounds a subsequent shift count

```c filename=shift.c
uint32 shift32(uint32 x, uint32 d) { return x << (d >> 27u); }
uint64 shift64(uint64 x, uint64 d) { return x << (d >> 58ULL); }
```

```click
verifying "shift.c";

uint32 shift32(uint32 x, uint32 d) { ensures true; }
uint64 shift64(uint64 x, uint64 d) { ensures true; }
```

```expect
pass
```
