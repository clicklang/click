# A signed zero result fits after checking the shift count

```c filename=shift.c
int32 shift32(int32 count) { return 0 << count; }
int64 shift64(int64 count) { return 0LL << count; }
```

```click
verifying "shift.c";

int32 shift32(int32 count) {
    requires 0 <= count;
    requires count < 32;
    ensures true;
}

int64 shift64(int64 count) {
    requires 0i64 <= count;
    requires count < 64i64;
    ensures true;
}
```

```expect
pass
```
