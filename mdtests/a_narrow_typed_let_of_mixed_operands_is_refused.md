# A narrow typed let of mixed operands is refused

At an 8- or 16-bit type, arithmetic is that type's own operator (decision
G2), so its operands must be of that type. `let s: uint8 = x + 1;` with an
`int32` `x` would have to convert `x`, and a conversion that can change a
value is written: the `let` is refused, naming the operand and the
conversion to write. With the conversion written, `(x as uint8) + 1` is the
`uint8` sum (`mdtests/a_written_narrow_conversion_makes_mixed_arithmetic_native.md`).

```c filename=a_narrow_typed_let_of_mixed_operands_is_refused.c
uint8 f(int32 x) { return x + 1; }
```

```click
verifying "a_narrow_typed_let_of_mixed_operands_is_refused.c";

uint8 f(int32 x) {
    let s: uint8 = x + 1;
    ensures result == s;
}
```

```expect
fail: `let s: uint8` does arithmetic at uint8, which is uint8's own operator and needs uint8 operands, but `x` is int32; write the conversion explicitly, as in `x as uint8`, or compute at a wider type and convert the result
```
