# Loop exit resource arguments

One exit changes cur to q. The joined resource cannot be passed as a cursor at the entry pointer p.

```c filename=loop_exit_resource_argument_rejects_entry_pointer.c
void choose(int32 *p, int32 *q, int32 *anchor, int32 flag) {
    int32 *cur = p;
    while (1) {
        if (flag) { cur = q; break; }
        else { break; }
    }
}
```

```click
verifying "loop_exit_resource_argument_rejects_entry_pointer.c";
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
    have b.tag == old(a.tag) by normalize();
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
            if flag != 0 {
                unfold(c);
                step(); step();
                let d = fold(cursor(cur, anchor), { tag: 0 });
                step();
            } else {
                step(); step();
            }
        }
    }
    let { b: b } = keep(p, anchor, { a: c });
    unfold(b);
    execute(); simp();
}
```

```expect
fail: named resource instance does not match its contract
```
