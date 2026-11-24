# XOR with an equal literal is still a zero divisor

```c filename=arithmetic.c
int32 divide(int32 n, int32 k) { return n / (k ^ 1); }
```

```click
verifying "arithmetic.c";

int32 divide(int32 n, int32 k) { requires k == 1; ensures true; }
```

```expect
fail: division by zero
```
