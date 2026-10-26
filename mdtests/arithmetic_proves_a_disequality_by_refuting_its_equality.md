# arithmetic proves a disequality by refuting its equality

`a != b` holds when the premises refute `a == b`: `k < j` gives `k != j`,
because `k == j` with `k < j` is a linear contradiction. `solve() using`
proves it from the listed premises, and the omitted proof from the connected facts, as
`intro()`, which adds `k == j` and leaves `false`, and an arithmetic
certificate for `false`. This holds for machine and `Integer` operands.

```click
theorem native_lt_neq(k: int32, j: int32) {
    requires k < j;
    ensures k != j;
}

theorem integer_lt_neq(k: Integer, j: Integer) {
    requires k < j;
    ensures k != j;
}

theorem integer_lt_neq_arithmetic(k: Integer, j: Integer) {
    requires k < j;
    ensures k != j by { solve() using { k < j; }; }
}

theorem native_lt_neq_arithmetic(k: int32, j: int32) {
    requires k < j;
    ensures k != j by { solve() using { k < j; }; }
}

theorem observed_successor_neq(k: uint64, j: uint64) {
    requires to_integer(k) + 1 <= to_integer(j);
    ensures k != j;
}

theorem written_negation(k: int64, j: int64) {
    requires k < j;
    ensures not (k == j);
}
```

```expect
pass
```
