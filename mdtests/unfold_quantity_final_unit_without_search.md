# Unfolding a symbolic quantity decides its final unit without search

Unfolding `amount of bundle(n)` takes its last unit, so it needs
`amount == 1`. The check is an exact lookup or the kernel's condition
decision: in `probe` the `requires` decides it; in `probe_have` the
`requires` states a disjunction the decision cannot use, and a `have` states
the unit first.

```c filename=unfold_quantity_final_unit.c
void probe(int32 amount, int32 n) {}
void probe_have(int32 amount, int32 n) {}
```

```click
abstract resource atom();
resource inner(n: int32) {
    owns atom();
    fact n == 3;
}
resource bundle(n: int32) {
    owns inner(n);
}
verifying "unfold_quantity_final_unit.c";
void probe(int32 amount, int32 n) {
    requires 0 < amount and amount < 2;
    owns amount of bundle(n);
} by {
    unfold(amount of bundle(n));
    execute();
    fold(bundle(n));
}
void probe_have(int32 amount, int32 n) {
    requires 0 <= amount and (amount == 1 or amount == 2) and amount != 2;
    owns amount of bundle(n);
} by {
    have amount == 1;
    unfold(amount of bundle(n));
    execute();
    fold(bundle(n));
}
```

```expect
pass
```
