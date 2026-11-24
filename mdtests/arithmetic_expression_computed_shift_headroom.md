# Signed shift headroom follows an inline cap or a remainder

```c filename=arithmetic.c
int32 cap(int32 k) { return 1 << (k < 16 ? k : 15); }
int32 cap_unsigned(uint32 k) { return 1 << (k < 16u ? k : 15u); }
int32 rem_unsigned(uint32 k) { return 1 << (k % 16u); }
int32 rem_wide_unsigned(uint64 k) { return 1 << (k % 16ULL); }
int64 rem_signed(int64 k) { return 1LL << (k % 16LL); }
```

```click
verifying "arithmetic.c";

int32 cap(int32 k) { requires k >= 0; ensures true; }
int32 cap_unsigned(uint32 k) { ensures true; }
int32 rem_unsigned(uint32 k) { ensures true; }
int32 rem_wide_unsigned(uint64 k) { ensures true; }
int64 rem_signed(int64 k) { requires k >= 0; ensures true; }
```

```expect
pass
```
