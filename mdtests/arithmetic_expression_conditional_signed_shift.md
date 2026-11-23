# A signed left shift retains the guard on an inline expression

```c filename=arithmetic.c
int32 shift32(int32 n, uint32 d) {
    return (d < 31u && n >= 0 && n <= (2147483647 >> d)) ? n << d : 0;
}

int64 shift64(int64 n, uint64 d) {
    return d < 63uLL && n >= 0 && n <= (9223372036854775807LL >> d) && (n << d) != 0;
}
```

```click
verifying "arithmetic.c";

int32 shift32(int32 n, uint32 d) { ensures true; }
int64 shift64(int64 n, uint64 d) { ensures true; }
```

```expect
pass
```
