# Fielded folds distinguish entry and current arguments

An explicit-field constructor reads `old(p)` at function entry after C assigns
`p`; ordinary arguments still use the execution cursor.

```c filename=probe.c
void probe(int *p, int *q) { p = q; }
void scalar(int n) { n = 8; }
void current(int *p, int *q) { p = q; }
```
```click
verifying "probe.c";
spec enum SavedPointer { At(int32*), }
resource saved_at(p: int32*) {
    field model: SavedPointer;
    fact model == SavedPointer::At(p);
}
void probe(int32* p, int32* q) {
    owns saved: saved_at(p);
    ensures saved.model == old(saved.model);
} by {
    unfold(saved);
    step();
    let saved = fold(saved_at(old(p)), { model: old(saved.model) });
    execute(); simp();
}
resource saved_index(n: int32) {
    field value: int32;
    fact value == n;
}
void scalar(int32 n) {
    owns saved: saved_index(n);
    ensures saved.value == old(saved.value);
} by {
    unfold(saved);
    step();
    let saved = fold(saved_index(old(n)), { value: old(saved.value) });
    execute(); simp();
}
void current(int32* p, int32* q) {
    owns saved: saved_at(q);
    ensures saved.model == old(saved.model);
} by {
    unfold(saved);
    step();
    let saved = fold(saved_at(p), { model: old(saved.model) });
    execute(); simp();
}
```
```expect
pass
```
