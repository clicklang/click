# Opening a returned resource does not undo a callee write

The callee can change the consumed cell. Caching its returned load must not
identify it with the value before the call.

```c filename=unfold_returned_resource_keeps_changed_cell.c
void keep(int32 *anchor) { *anchor = 7; }
void call(int32 *anchor, int32 *other) { keep(anchor); }
```

```click
verifying "unfold_returned_resource_keeps_changed_cell.c";
resource cell(p: int32*) { field tag: int32; owns *p; }
void keep(int32* anchor) {
    consumes a: cell(anchor);
    produces b: cell(anchor);
} by {
    unfold(a);
    step();
    let b = fold(cell(anchor), { tag: old(a.tag) });
    execute(); simp();
}
void call(int32* anchor, int32* other) {
    consumes c: cell(anchor);
    owns *other;
    produces *anchor;
    ensures *anchor == old(*anchor);
} by {
    let { b: d } = step(keep(anchor), { a: c });
    unfold(d);
    have *anchor == old(*anchor);
    execute(); simp();
}
```

```expect
fail: `simp` failed
```
