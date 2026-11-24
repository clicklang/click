# Rounding an integer up to the exclusive cast endpoint is unsafe

```c filename=arithmetic.c
int32 via_float(int32 x) { return (int32)(float)x; }
```

```click
verifying "arithmetic.c";
int32 via_float(int32 x) { requires x <= 2147483584; ensures true; }
```

```expect
fail: float32_from_bits(0x4f000000)
```
