# An unsigned division exposes its nonzero-divisor obligation

```c filename=divide.c
uint32 divide(uint32 x, uint32 y) { return x / y; }
```

```click
verifying "divide.c";
uint32 divide(uint32 x, uint32 y) {
    requires y != 0u32;
    ensures result == x / y;
} by {
    step() by { known(); }
    known();
}
```

```expect
pass
```
