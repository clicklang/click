# Reusing a produced name does not preserve its old resource index

```c filename=call_produced_reuse_requires_new_argument.c
void retarget(int32 *p, int32 *q, int32 *anchor) {}
void call(int32 *p, int32 *q, int32 *anchor) { retarget(p, q, anchor); retarget(p, q, anchor); }
```

```click
verifying "call_produced_reuse_requires_new_argument.c";
resource cursor(p: int32*, anchor: int32*) {
    field tag: int32;
    owns *anchor;
}
void retarget(int32* p, int32* q, int32* anchor) {
    consumes a: cursor(p, anchor);
    produces b: cursor(q, anchor);
    ensures b.tag == old(a.tag);
} by {
    unfold(a);
    let b = fold(cursor(q, anchor), { tag: old(a.tag) });
    execute(); simp();
}
void call(int32* p, int32* q, int32* anchor) {
    requires p != q;
    consumes c: cursor(p, anchor);
    produces *anchor;
} by {
    let { b: c } = step(retarget(p, q, anchor), { a: c });
    let { b: d } = step(retarget(p, q, anchor), { a: c });
    unfold(d);
    execute(); simp();
}
```

```expect
fail: named resource instance does not match its contract
```
