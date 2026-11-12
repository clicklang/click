# A total specification quotient does not define the C division

The contract's `a / b` is total, but the C `a / b` it describes is still
undefined at a zero divisor. Execution refuses it.

```c filename=a_total_specification_quotient_does_not_define_the_c_division.c
uint32 quotient(uint32 a, uint32 b) {
    return a / b;
}
```

```click
verifying "a_total_specification_quotient_does_not_define_the_c_division.c";

uint32 quotient(uint32 a, uint32 b) {
    ensures result == a / b;
}
```

```expect
fail: unproved obligation: `b != 0`
```
