# A produced resource can reuse its consumed input name

The returned instance uses its new pointer index and retains only the model
relation promised by the callee. Reusing the caller name preserves entry-state
observations without retaining the old resource arguments.

```c filename=call_produced_reuses_consumed_name.c
void retarget(int32 *p, int32 *q, int32 *anchor) {}
void call(int32 *p, int32 *q, int32 *anchor) { retarget(p, q, anchor); }
```

```click
verifying "call_produced_reuses_consumed_name.c";
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
    consumes c: cursor(p, anchor);
    produces *anchor;
} by {
    let { b: c } = step(retarget(p, q, anchor), { a: c });
    have c.tag == old(c.tag) by { simp(); }
    unfold(c);
    execute(); simp();
}
```

```expect
pass
```
