# An in-range unsigned count does not make a signed result fit

```c filename=arithmetic.c
int32 shift(int32 n, uint32 d) { return n << d; }
```

```click
verifying "arithmetic.c";

int32 shift(int32 n, uint32 d) { requires n == 1; requires d == 31u32; ensures true; }
```

```expect
fail: signed overflow
```
