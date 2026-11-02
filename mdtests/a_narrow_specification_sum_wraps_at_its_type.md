# A narrow specification sum wraps at its type

`let s: uint8 = a + b;` is the `uint8` operator (decision G2), whose value
is the sum modulo 2^8. It is the exact sum only where the sum fits, so the
Integer claim needs that range; with it, the in-range identity gives the
exact sum.

```c filename=a_narrow_specification_sum_wraps_at_its_type.c
uint8 wrapped(uint8 a, uint8 b) { return a + b; }
uint8 fitting(uint8 a, uint8 b) { return a + b; }
```

```click
verifying "a_narrow_specification_sum_wraps_at_its_type.c";

uint8 wrapped(uint8 a, uint8 b) {
    let s: uint8 = a + b;
    ensures to_integer(s) == to_integer(a) + to_integer(b);
}

uint8 fitting(uint8 a, uint8 b) {
    requires to_integer(a) + to_integer(b) <= 255;
    let s: uint8 = a + b;
    ensures to_integer(s) == to_integer(a) + to_integer(b);
}
```

```expect
fail: failed for `wrapped.ensures_0`
```
