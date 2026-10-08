# Integer arguments preserve logical specification reads

Logical heap observations follow specification read semantics. Capturing one
does not execute a C load or grant read authority.

```click
theorem identity(n: Integer) {
    ensures n == n by simp;
}

theorem logical_read(p: uint32*) {
    ensures to_integer(p[0]) == to_integer(p[0]) by {
        apply(identity(to_integer(p[0])));
    }
}
```

```expect
pass
```
