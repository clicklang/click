# Post-return folds retain immutable argument facts of held resources

`Positive` has no memory to read: its fact is about the value captured when
the resource was formed. Certification of the post-return proof must recover
that fact from the held resource, without assuming current-memory invariants.

```c filename=argument.c
int f(int *p) { return 0; }
```
```click
verifying "argument.c";
resource Positive(n: int32) { fact 1 <= n; }
resource Cell(p: int32*) {
    field tag: int32;
    owns p[0..1];
    owns Positive(p[0]);
}
int32 f(int32* p) {
    consumes before: Cell(p);
    produces after: Cell(p);
    ensures result == 0;
} by {
    unfold(before);
    execute();
    have result == 0 by normalize();
    let after = fold(Cell(p), { tag: 1 });
    simp();
}
```
```expect
pass
```
