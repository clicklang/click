# Cast safety uses the finite float self-subtraction and self-division bounds

```c filename=arithmetic.c
int32 difference(float x) { return (int32)(x - x); }
int32 quotient(float x) { return (int32)(x / x); }
int32 quotient_wide(double x) { return (int32)(x / x); }
```

```click
verifying "arithmetic.c";

int32 difference(float x) { requires isfinite(x); ensures true; }
int32 quotient(float x) { requires isfinite(x); requires x != float32_from_bits(0); ensures true; }
int32 quotient_wide(double x) { requires isfinite(x); requires x != float64_from_bits(0u64); ensures true; }
```

```expect
pass
```
