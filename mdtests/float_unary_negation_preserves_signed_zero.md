# Click unary negation uses IEEE sign negation

The reciprocal distinguishes negative zero from positive zero. A pure Click
call also keeps the same unary operation as the C function. The symbolic
contracts assume self-equality to exclude NaN without asking automation to
derive that fact from a classification predicate.

```c filename=float_unary_negation.c
float negate32(float x) { return -x; }
double negate64(double x) { return -x; }
```

```click
verifying "float_unary_negation.c";

function flip(x: double) -> double { -x }

float negate32(float x) {
    requires -x == -x;
    ensures result == -x;
}

double negate64(double x) {
    requires -x == -x;
    ensures result == flip(x) by { step(); unfold(flip(x)); solve(); }
}

theorem negate_zero() {
    ensures float32_from_bits(0x3f800000) / -float32_from_bits(0) == float32_from_bits(0xff800000) by { normalize(); }
    ensures float64_from_bits(0x3ff0000000000000) / -float64_from_bits(0) == float64_from_bits(0xfff0000000000000) by { normalize(); }
}
```

```expect
pass
```
