# A written narrow conversion makes mixed arithmetic native

The companion of
`mdtests/a_narrow_typed_let_of_mixed_operands_is_refused.md`: with the
conversion written, `(x as uint8) + 1` adds two `uint8` operands, so it is the
`uint8` sum (decision G2). C computes `x + 1` in `int` and converts the
result; the two agree because the conversion distributes over the sum.

```c filename=a_written_narrow_conversion_makes_mixed_arithmetic_native.c
uint8 f(int32 x) { return (uint8) x + 1; }
```

```click
verifying "a_written_narrow_conversion_makes_mixed_arithmetic_native.c";

uint8 f(int32 x) {
    let s: uint8 = (x as uint8) + 1;
    ensures result == s;
}
```

```expect
pass
```
