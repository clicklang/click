# Bounded signed left shifts

```c filename=shifts.c
int32 shift32(int32 x) { return x << 8; }
int64 shift64(int64 x) { return x << 8; }
int32 shift_with_domain(int32 x, int32 k) { return x << k; }
```

```click
verifying "shifts.c";

int32 shift32(int32 x) {
    requires 0 <= x;
    requires x <= 255;
    ensures result == x << 8;
}

int64 shift64(int64 x) {
    requires 0i64 <= x;
    requires x <= 255i64;
    ensures result == x << 8;
}

int32 shift_with_domain(int32 x, int32 k) {
    requires defined(x << k);
    ensures result == x << k;
}
```

```expect
pass
```
