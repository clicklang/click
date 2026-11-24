# Two distinct operands can have a negative product

```c filename=arithmetic.c
uint32 product(float x, float y) { return (uint32)(x * y); }
```

```click
verifying "arithmetic.c";

uint32 product(float x, float y) {
    requires x >= float32_from_bits(0xc0000000);
    requires x <= float32_from_bits(0x40000000);
    requires y >= float32_from_bits(0xc0000000);
    requires y <= float32_from_bits(0x40000000);
    ensures true;
}
```

```expect
fail: explicit prerequisite proof
```
