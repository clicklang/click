# A produced name cannot overwrite another live instance

```c filename=call_produced_reuse_rejects_live_name.c
void retarget(int32 *p, int32 *q, int32 *anchor) {}
void call(int32 *p, int32 *q, int32 *anchor, int32 *other) { retarget(p, q, anchor); }
```

```click
verifying "call_produced_reuse_rejects_live_name.c";
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
void call(int32* p, int32* q, int32* anchor, int32* other) {
    consumes a: cursor(p, anchor);
    consumes c: cursor(q, other);
    produces *anchor;
} by {
    let { b: c } = step(retarget(p, q, anchor), { a: a });
    unfold(c);
    execute(); simp();
}
```

```expect
fail: duplicate resource fact
```
