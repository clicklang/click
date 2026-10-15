# Observing a symbolic quantity decides its positivity without search

`observe(amount of bundle(n))` exposes the body only where `amount > 0`. The
check is an exact lookup or the kernel's condition decision: in `probe` the
`requires` decides it; in `probe_have` a `have` states it first. The nested
`observe(inner(n))` needs the exposed body.

```c filename=observe_quantity_positive.c
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
verifying "observe_quantity_positive.c";
void probe(int32 amount, int32 n) {
    requires 0 <= amount and 0 < amount;
    owns amount of bundle(n);
    ensures n == 3;
} by {
    observe(amount of bundle(n));
    observe(inner(n));
    execute();
}
void probe_have(int32 amount, int32 n) {
    requires 0 <= amount and (amount == 1 or amount == 2);
    owns amount of bundle(n);
    ensures n == 3;
} by {
    have 0 < amount;
    observe(amount of bundle(n));
    observe(inner(n));
    execute();
}
```

```expect
pass
```
