# A contract exit cannot return a folded composite and its body child

`f` holds only `wrap(p)`, whose body is `owns p[0..1]`. Returning both
`wrap(p)` and `p[0..1]` would hand the caller the cell twice, once directly
and once inside the composite. The returned clauses are consumed from the
final state as one multiset, so the second clause is refused.

```c filename=composite_child.c
int32 f(int32* p) {
    return 0;
}
```

```click
resource wrap(p: int32*) {
    owns p[0..1];
}
verifying "composite_child.c";
int32 f(int32* p) {
    owns wrap(p);
    produces p[0..1];
} by auto;
```

```expect
fail: missing resource fact
```
