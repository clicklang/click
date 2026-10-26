# A produced resource keeps its declared entry or return argument

```c filename=old_pointer.c
struct box { int *child; };
void split(struct box *p, int *q) { p->child = q; }
void caller(struct box *p, int *q) { split(p, q); }
```

```click
verifying "old_pointer.c";
spec enum Model { Empty, }
resource cell(p: int32*) { field model: Model; fact model == Model::Empty; }
resource holder(p: struct box*) {
    field model: Model;
    owns p->child;
    fact model == Model::Empty;
}
void split(struct box* p, int32* q) {
    consumes h: holder(p);
    produces p->child;
    produces t: cell(old(p->child));
    produces u: cell(p->child);
    ensures p->child == q;
} by {
    unfold(h);
    let t = fold(cell(p->child), { model: Model::Empty });
    step_until(function.exit);
    let u = fold(cell(p->child), { model: Model::Empty });
    solve();
}
void caller(struct box* p, int32* q) {
    consumes h: holder(p);
    produces p->child;
    produces t: cell(old(p->child));
    produces u: cell(p->child);
    ensures p->child == q;
} by {
    let { t: t, u: u } = step(split, { h: h });
}
```

```expect
pass
```
