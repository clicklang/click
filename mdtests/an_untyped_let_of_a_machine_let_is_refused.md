# An untyped `let` of arithmetic on a machine `let` is refused

`t` below is the `int32` `a`, so `t + 1` is arithmetic on a machine value
with no expected type, refused as `let u = a + 1;` would be. The diagnostic
names `t`'s type for the C operation. A `let` of an Integer gives later
arithmetic an Integer
(`mdtests/an_untyped_let_of_an_integer_has_the_integer_type.md`).

```click
theorem machine_chain(a: int32) {
    let t = a;
    let u = t + 1;
    ensures u > t by auto();
}
```

```expect
fail: untyped `let u` does arithmetic on a machine value; arithmetic takes its meaning from the type its result is used at, so write `let u: Integer = ...;` for the exact value or `let u: int32 = ...;` for the C operation
```
