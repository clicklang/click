# A typed `let` gives machine arithmetic its meaning

`let s: Integer = a + b;` expects an Integer, so `a + b` is the exact sum
`to_integer(a) + to_integer(b)` and `s >= a` holds for every nonnegative
`b` with no overflow bound. An untyped `let` of a plain machine value, or
of arithmetic on literals alone, needs no annotation: `t` is the `int32`
`a` and `k` is the Integer `8`. The `int32` annotation keeps the C sum
(`mdtests/a_machine_typed_let_keeps_the_c_operation.md`); without either the
binding is refused
(`mdtests/an_untyped_let_of_machine_arithmetic_is_refused.md`).

```click
theorem integer_sum(a: int32, b: int32) {
    let s: Integer = a + b;
    let t = a;
    let k = 5 + 3;
    requires 0 <= a;
    requires 0 <= b;
    ensures s >= a;
    ensures t == a;
    ensures k == 8;
}
```

```expect
pass
```
