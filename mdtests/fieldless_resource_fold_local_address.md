# Ordinary resource folds preserve local and parameter addresses

```c filename=resource_address.c
void observe(int32 *p) {}
void local(void) { int32 x = 7; observe(&x); x = 9; }
void parameter(int32 x) { x = 7; observe(&x); x = 9; }
```

```click
verifying "resource_address.c";
resource cell_at(p: int32*) {}
void observe(int32* p) {
    ensures 1 == 1;
} by { execute(); simp(); }
void local() {
    ensures 1 == 1;
} by {
    step(); step();
    fold(cell_at(&x));
    step(observe(&x), {});
    step();
    unfold(cell_at(&x));
    fold(cell_at(&x));
    unfold(cell_at(&x));
    execute(); simp();
}
void parameter(int32 x) {
    ensures 1 == 1;
} by {
    step();
    fold(cell_at(&x));
    step(observe(&x), {});
    step();
    unfold(cell_at(&x));
    fold(cell_at(&x));
    unfold(cell_at(&x));
    execute(); simp();
}
```

```expect
pass
```
