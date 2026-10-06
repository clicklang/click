# Integer theorem arguments captured from machine observations

Native argument evaluation keeps its definedness obligations even when the
callee's conclusion is reflexive. Mathematical values are captured at the
application site, including observations of returned values.

```c filename=observed.c
int32 unchanged(int32 x) { return x; }
```

```click
theorem integer_reflexive(z: Integer) {
    ensures z == z by simp;
}

theorem observe64(x: int64) {
    requires defined(x + 1i64);
    ensures to_integer(x + 1i64) == to_integer(x + 1i64) by {
        apply(integer_reflexive(to_integer(x + 1i64)));
    }
}

verifying "observed.c";
int32 unchanged(int32 x) {
    requires defined(x + 1);
    ensures result == x;
} by {
    apply(integer_reflexive(to_integer(x + 1)));
    apply(integer_truncation_identity(to_integer(x), 3));
    execute();
    apply(integer_reflexive(to_integer(result)));
    simp();
}
```

```expect
pass
```
