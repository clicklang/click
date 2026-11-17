# Exact proposition propagation decides the final unfold unit

The exact disjunction and the refutation of its second arm propagate
`amount == 1`. Ordinary unfold can use that fact without a case split.

```c filename=unfold_quantity_final_unit_refused.c
void probe(int32 amount, int32 n) {}
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
verifying "unfold_quantity_final_unit_refused.c";
void probe(int32 amount, int32 n) {
    requires 0 <= amount and (amount == 1 or amount == 2) and amount != 2;
    owns amount of bundle(n);
} by {
    unfold(amount of bundle(n));
    step_until(function.exit);
    fold(bundle(n));
}
```

```expect
pass
```
