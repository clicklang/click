# Unfolding a symbolic quantity refuses an undecided final unit

The `requires` implies `amount == 1` only by a case split, which the unfold
does not search for, so it is refused at the unit.

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
    execute();
    fold(bundle(n));
}
```

```expect
fail: `unfold(amount of bundle(n))` Requires count(bundle(n)) == amount
```
