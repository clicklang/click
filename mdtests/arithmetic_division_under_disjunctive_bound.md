# Close can split a written divisor range into safe cases

```c filename=arithmetic.c
int32 divide(int32 n, int32 d) { return n / d; }
int64 remainder(int64 n, int64 d) { return n % d; }
```

```click
verifying "arithmetic.c";

int32 divide(int32 n, int32 d) {
    requires d > 0 or d < -1;
    ensures true;
}
int64 remainder(int64 n, int64 d) {
    requires d > 0 or d < -1;
    ensures true;
}

theorem safe_divisor(d: int32) {
    requires d > 0 or d < -1;
    ensures d != 0 and d != -1 by { close(); }
}
```

```expect
pass
```
