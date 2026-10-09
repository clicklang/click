# Loop exit resource arguments

One exit establishes p == q and hands back cursor(p, anchor) while cur is q. Rebinding uses that exit's checked equality, then keeps the resource argument tied to the joined cur.

```c filename=loop_exit_resource_argument_uses_exit_alias.c
void choose(int32 *p, int32 *q, int32 *anchor, int32 flag) {
    int32 *cur = p;
    while (1) {
        if (p == q) { cur = q; break; }
        else { break; }
    }
}
```

```click
verifying "loop_exit_resource_argument_uses_exit_alias.c";
resource cursor(p: int32*, anchor: int32*) {
    field tag: int32;
    owns *anchor;
}
tactic keep(p: int32*, anchor: int32*) {
    consumes a: cursor(p, anchor);
    produces b: cursor(p, anchor);
    ensures b.tag == old(a.tag);
} by {
    unfold(a);
    let b = fold(cursor(p, anchor), { tag: old(a.tag) });
    have b.tag == old(a.tag) by { normalize(); }
}
void choose(int32* p, int32* q, int32* anchor, int32 flag) {
    consumes c: cursor(p, anchor);
    produces *anchor;
} by {
    execute_until(loop(0));
    loop {
        owns c: cursor(cur, anchor);
        decreases 0;
        preserve by {
            if p == q {
                unfold(c);
                step(); step();
                let d = fold(cursor(p, anchor), { tag: 0 });
                step();
            } else {
                step(); step();
            }
        }
    }
    let { b: b } = keep(cur, anchor, { a: c });
    unfold(b);
    execute(); simp();
}
```

```expect
pass
```
