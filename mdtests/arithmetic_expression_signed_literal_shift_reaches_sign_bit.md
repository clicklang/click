# A valid count can still shift a signed literal into the sign bit

```c filename=arithmetic.c
int32 shift(int32 k) { return 1 << k; }
```

```click
verifying "arithmetic.c";

int32 shift(int32 k) { requires k == 31; ensures true; }
```

```expect
fail: signed overflow
```
