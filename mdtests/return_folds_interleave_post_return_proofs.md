# Each returned fold can consume a proof completed after the preceding fold

```c filename=return_interleaved_folds.c
int f(int *p, int *q) { return 0; }
int g(int *p, int *q) { return 0; }
```
```click
verifying "return_interleaved_folds.c";
function reflexive(p: int32*) -> int32 { if p == p { 1 } else { 0 } }
resource Cell(p: int32*) {
    field tag: int32;
    owns p[0..1];
    fact reflexive(p) == 1;
}
resource PlainCell(p: int32*) {
    field tag: int32;
    owns p[0..1];
}
int32 f(int32* p, int32* q) {
    consumes p[0..1];
    consumes q[0..1];
    produces left: Cell(p);
    produces right: Cell(q);
    ensures result == 0;
} by {
    execute();
    have reflexive(p) == 1 by { unfold(reflexive(p)); normalize(); }
    let left = fold(Cell(p), { tag: 1 });
    have reflexive(q) == 1 by { unfold(reflexive(q)); normalize(); }
    let right = fold(Cell(q), { tag: 2 });
    simp();
}
int32 g(int32* p, int32* q) {
    consumes p[0..1];
    consumes q[0..1];
    produces left: PlainCell(p);
    produces right: Cell(q);
    ensures result == 0;
} by {
    execute();
    let left = fold(PlainCell(p), { tag: 1 });
    have reflexive(q) == 1 by { unfold(reflexive(q)); normalize(); }
    let right = fold(Cell(q), { tag: 2 });
    simp();
}
```
```expect
pass
```
