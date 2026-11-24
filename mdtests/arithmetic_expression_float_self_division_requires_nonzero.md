# Finite values include zero, and zero divided by itself gives NaN

```c filename=arithmetic.c
int32 convert(float x) { return (int32)(x / x); }
```

```click
verifying "arithmetic.c";
int32 convert(float x) { requires isfinite(x); ensures true; }
```

```expect
fail: explicit prerequisite proof
```
