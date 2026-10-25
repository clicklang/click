# A scalar model field gives an ordinary owned resource quantity

Unfold and refold preserve an arbitrary quantity. Packaging two credits checks
and consumes those two credits; the scalar model does not create ownership.

```c filename=resource_model_quantity.c
void keep(int32* p) { }
void package(int32* p) { }
void empty(int32* p) { }
void keep_wrapper(int32* p) { }
```

```click
verifying "resource_model_quantity.c";
abstract resource credit(p: int32*);
resource bundle(p: int32*) {
    field amount: int32;
    owns amount of credit(p);
    fact amount >= 0;
}
resource label(p: int32*) {
    field amount: int32;
}
resource wrapper(p: int32*) {
    field amount: int32;
    owns label: label(p);
    owns amount of credit(p);
    fact label.amount == amount;
    fact amount >= 0;
}
void keep(int32* p) {
    owns s: bundle(p);
    ensures s.amount == old(s.amount);
} by {
    let { amount: n } = unfold(s);
    step_until(function.exit);
    let s = fold(bundle(p), { amount: n });
    solve();
}
void package(int32* p) {
    consumes 2 of credit(p);
    produces s: bundle(p);
    ensures s.amount == 2;
} by {
    let s = fold(bundle(p), { amount: 2 });
}
void empty(int32* p) {
    produces s: bundle(p);
    ensures s.amount == 0;
} by {
    let s = fold(bundle(p), { amount: 0 });
}
void keep_wrapper(int32* p) {
    owns s: wrapper(p);
    ensures s.amount == old(s.amount);
} by {
    let { amount: n, label: l } = unfold(s);
    step_until(function.exit);
    let s = fold(wrapper(p), { amount: n }, { label: l });
    solve();
}
```

```expect
pass
```
