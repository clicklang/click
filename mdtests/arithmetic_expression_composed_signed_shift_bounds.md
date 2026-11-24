# Signed left shifts use the indexed upper bounds of their operands

```c filename=arithmetic.c
int32 tighter(int32 k) { return 1 << k; }
int32 inclusive(int32 k) { return 1 << k; }
int32 masked(int32 k) { return 1 << (k & 15); }
int32 wide_count(uint64 k) { return 1 << k; }
int32 tighter_wide_count(uint64 k) { return 1 << k; }
int64 narrow_count(uint32 k) { return 1LL << k; }
int32 bounded(int32 n, int32 k) { return n << k; }
```

```click
verifying "arithmetic.c";

int32 tighter(int32 k) { requires k >= 0; requires k < 16; ensures true; }
int32 inclusive(int32 k) { requires k >= 0; requires k <= 30; ensures true; }
int32 masked(int32 k) { ensures true; }
int32 wide_count(uint64 k) { requires k < 31u64; ensures true; }
int32 tighter_wide_count(uint64 k) { requires k <= 15u64; ensures true; }
int64 narrow_count(uint32 k) { requires k < 63u32; ensures true; }
int32 bounded(int32 n, int32 k) {
    requires n >= 0;
    requires n <= 3;
    requires k >= 0;
    requires k <= 4;
    ensures true;
}
```

```expect
pass
```
