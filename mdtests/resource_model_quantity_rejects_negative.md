# Negative scalar models cannot create negative resource quantities

```c filename=resource_model_quantity_rejects_negative.c
void package(int32* p) { }
```

```click
verifying "resource_model_quantity_rejects_negative.c";
abstract resource credit(p: int32*);
resource bundle(p: int32*) {
    field amount: int32;
    owns amount of credit(p);
}
void package(int32* p) {
    produces s: bundle(p);
} by {
    let s = fold(bundle(p), { amount: -1 });
    execute();
    simp();
}
```

```expect
fail: declared resource quantity is not known nonnegative
```
