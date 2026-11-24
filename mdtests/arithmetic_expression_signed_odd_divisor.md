# A literal set bit rules out a zero divisor

```c filename=arithmetic.c
int32 divide(int32 x, int32 y) {
    return x != (-2147483647 - 1) ? x / (y | 1) : 0;
}

int64 remainder(int64 x, int64 y) {
    return x != (-9223372036854775807LL - 1) ? x % (1 | y) : 0;
}
```

```click
verifying "arithmetic.c";

int32 divide(int32 x, int32 y) { ensures true; }
int64 remainder(int64 x, int64 y) { ensures true; }
```

```expect
pass
```
