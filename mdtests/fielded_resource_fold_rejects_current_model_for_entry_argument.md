# An entry argument cannot use the reassigned pointer's model

```c filename=probe.c
void probe(int *p, int *q) { p = q; }
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
    requires p != q;
    ensures saved.model == old(saved.model);
} by {
    unfold(saved);
    step();
    let saved = fold(saved_at(old(p)), { model: SavedPointer::At(q) });
    execute(); simp();
}
```
```expect
fail: fold requires the instance body facts for the proposed fields
```
