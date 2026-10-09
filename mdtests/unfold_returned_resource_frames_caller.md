# Opening a returned resource preserves the caller frame

An unfold only caches existing loads. The caller-owned cell stays unchanged
without extra separation or transport premises.

```c filename=unfold_returned_resource_frames_caller.c
void keep(int32 *anchor) {}
void call(int32 *anchor, int32 *other) { keep(anchor); }
```

```click
verifying "unfold_returned_resource_frames_caller.c";
resource cell(p: int32*) { field tag: int32; owns *p; }
void keep(int32* anchor) {
    consumes a: cell(anchor);
    produces b: cell(anchor);
} by {
    unfold(a);
    let b = fold(cell(anchor), { tag: old(a.tag) });
    execute(); simp();
}
void call(int32* anchor, int32* other) {
    consumes c: cell(anchor);
    owns *other;
    produces *anchor;
    ensures *other == old(*other);
} by {
    let { b: d } = step(keep(anchor), { a: c });
    unfold(d);
    have *other == old(*other) by { simp(); }
    execute(); simp();
}
```

```expect
pass
```
