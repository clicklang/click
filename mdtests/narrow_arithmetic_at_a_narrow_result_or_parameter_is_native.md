# Narrow arithmetic at a narrow result or parameter is native

A pure function's body is at its result type and an argument at its
parameter's type (decision G2). At 8 or 16 bits, arithmetic over values of
that type is the type's operator, so `add8`'s body `a + b` wraps modulo
2^8 (`200 + 100` is `44`), and `id8(a + b)` passes the `uint8` sum, the
same value as a `uint8` `let` of `a + b`. A comparison that does
arithmetic still reads as Integer.

```click
function add8(a: uint8, b: uint8) -> uint8 {
    a + b
}

function id8(x: uint8) -> uint8 {
    x
}

theorem body_is_the_uint8_sum(a: uint8, b: uint8) {
    let s: uint8 = a + b;
    ensures add8(a, b) == s by { unfold(add8(a, b)); solve(); };
}

theorem body_wraps() {
    ensures add8(200u8, 100u8) == 44u8 by { unfold(add8(200u8, 100u8)); solve(); };
}

theorem argument_is_the_uint8_sum(a: uint8, b: uint8) {
    let s: uint8 = a + b;
    ensures id8(a + b) == s by { unfold(id8(a + b)); solve(); };
}
```

```expect
pass
```
