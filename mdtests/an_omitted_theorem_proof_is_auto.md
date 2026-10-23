# an omitted theorem proof is auto

Omitting a pure theorem's `ensures` proof uses the default prover, `auto`,
the same closer `by auto();` runs: each claim below closes with its proof
omitted, as it does with `by auto();`.

```click
theorem omitted(left: int32, right: int32) {
    requires defined(left + right);
    ensures to_integer(left + right) == to_integer(left) + to_integer(right);
}

theorem omitted_order(a: int32, b: int32, c: int32) {
    requires a < b;
    requires b < c;
    ensures to_integer(a) + 2 <= to_integer(c);
}

theorem omitted_unsigned_sum(a: uint32, b: uint32) {
    requires to_integer(a) + to_integer(b) <= 4294967295;
    ensures to_integer(a + b) == to_integer(a) + to_integer(b);
}

theorem omitted_disequality(k: Integer, j: Integer) {
    requires k < j;
    ensures k != j;
}
```

```expect
pass
```
