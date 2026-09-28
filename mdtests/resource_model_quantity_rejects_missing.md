# A model quantity does not manufacture missing credits

```c filename=resource_model_quantity_rejects_missing.c
void package(int32* p) { }
```

```click
verifying "resource_model_quantity_rejects_missing.c";
abstract resource credit(p: int32*);
resource bundle(p: int32*) {
    field amount: int32;
    owns amount of credit(p);
    fact amount >= 0;
}
void package(int32* p) {
    consumes credit(p);
    produces s: bundle(p);
    ensures s.amount == 2;
} by {
    let s = fold(bundle(p), { amount: 2 });
    execute();
    simp();
}
```

```expect
fail: fold requires ownership of the complete instance body
```
