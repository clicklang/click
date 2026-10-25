# An untyped `let` of machine arithmetic is refused

Arithmetic on machine values takes its meaning from the type its result is
used at, and an untyped `let` gives its value no type: `a + b` below could
be the exact Integer sum or the partial `int32` sum. The binding is refused
and the diagnostic names both annotations, with the operand's type for the
C operation. `mdtests/a_typed_let_gives_machine_arithmetic_its_meaning.md`
writes each one.

```click
theorem untyped_sum(a: int32, b: int32) {
    let s = a + b;
    requires 0 <= a;
    requires 0 <= b;
    ensures s >= a by auto();
}
```

```expect
fail: untyped `let s` does arithmetic on a machine value; arithmetic takes its meaning from the type its result is used at, so write `let s: Integer = ...;` for the exact value or `let s: int32 = ...;` for the C operation
```
