# A cast can reuse the stronger bounds on its quotient

```c filename=arithmetic.c
int32 f(float y) { return (int32)(1.0f / y); }
```

```click
verifying "arithmetic.c";
int32 f(float y) {
  requires float32_from_bits(0x3f800000) / y >= float32_from_bits(0);
  requires float32_from_bits(0x3f800000) / y <= float32_from_bits(0x3f800000);
  ensures true;
}
```

```expect
pass
```
