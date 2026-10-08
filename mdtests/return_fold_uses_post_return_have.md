# A returned fold uses a proved pure function fact
```c filename=return_derived_fold.c
int f(int *p) { return 0; }
```
```click
verifying "return_derived_fold.c";
function reflexive(p: int32*) -> int32 { if p == p { 1 } else { 0 } }
resource Cell(p: int32*) {
    field tag: int32;
    owns p[0..1];
    fact reflexive(p) == 1;
}
int32 f(int32* p) {
    consumes p[0..1];
    produces out: Cell(p);
    ensures result == 0;
} by {
    execute();
    have reflexive(p) == 1 by { unfold(reflexive(p)); normalize(); }
    let out = fold(Cell(p), { tag: 1 });
    simp();
}
```
```expect
pass
```
