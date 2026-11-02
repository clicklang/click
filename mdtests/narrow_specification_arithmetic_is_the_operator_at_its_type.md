# Narrow specification arithmetic is the operator at its type

Specification arithmetic takes its meaning from the type its result is used
at (`design/machine-integers.md`, decision G2). At an 8- or 16-bit type, as
in `let s: uint8 = a + b;`, `+ - * & | ^ ~` over operands of that type is
that type's operator, the native node `a +_u8 b`, which wraps modulo 2^8.
C computes the same sum in promoted `int` and converts it back; the
conversion distributes over the sum (R-dist with R-comp), so the C result
meets the native one at 8 and 16 bits and at either signedness.

```c filename=narrow_specification_arithmetic_is_the_operator_at_its_type.c
uint8 add8(uint8 a, uint8 b) { return a + b; }
int8 sub8(int8 a, int8 b) { return a - b; }
uint16 mix16(uint16 a, uint16 b) { return a ^ b; }
int16 not16(int16 a, int16 b) { return ~a & b; }
```

```click
verifying "narrow_specification_arithmetic_is_the_operator_at_its_type.c";

uint8 add8(uint8 a, uint8 b) {
    let s: uint8 = a + b;
    ensures result == s;
}

int8 sub8(int8 a, int8 b) {
    let d: int8 = a - b;
    ensures result == d;
}

uint16 mix16(uint16 a, uint16 b) {
    let m: uint16 = a ^ b;
    ensures result == m;
}

int16 not16(int16 a, int16 b) {
    let n: int16 = ~a & b;
    ensures result == n;
}
```

```expect
pass
```
