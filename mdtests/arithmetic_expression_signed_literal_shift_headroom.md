# A literal's signed left shift uses the stated count bound

```c filename=arithmetic.c
int32 shift32(int32 k) { return 1 << k; }
int64 shift64(uint64 k) { return 1LL << k; }
int32 shift_literal(int32 k) { return k >= 0 && k < 29 ? 6 << k : 0; }
```

```click
verifying "arithmetic.c";

int32 shift32(int32 k) { requires k >= 0; requires k < 31; ensures true; }
int64 shift64(uint64 k) { requires k < 63u64; ensures true; }
int32 shift_literal(int32 k) { ensures true; }
```

```expect
pass
```
