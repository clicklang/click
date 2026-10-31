# A machine-typed `let` keeps the C operation

`let s: int32 = a + b;` expects an `int32`, so `a + b` is C's signed sum,
which is undefined where it overflows. `s >= a` is that C value compared
natively, and nothing here bounds the sum, so the claim is not proved. With
`requires defined(a + b);` it is. The Integer twin is
`mdtests/a_typed_let_gives_machine_arithmetic_its_meaning.md`.

```click
theorem machine_sum(a: int32, b: int32) {
    let s: int32 = a + b;
    requires 0 <= a;
    requires 0 <= b;
    ensures s >= a;
}
```

```expect
fail: not established: `a + b`
```
