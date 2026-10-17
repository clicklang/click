# Loop exit resource arguments

One exit establishes C address equality and hands back a cursor at p's address
while cur is q. The cursor's phantom position is a numeric address, so exit
rebinding uses that equality without asserting equal pointer designations.
The anchor remains a complete pointer because it carries the owned cell.

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
resource cursor(position: uint64, anchor: int32*) {
    field tag: int32;
    owns *anchor;
}
tactic keep(p: int32*, anchor: int32*) {
    consumes a: cursor(address(p), anchor);
    produces b: cursor(address(p), anchor);
    ensures b.tag == old(a.tag);
} by {
    unfold(a);
    let b = fold(cursor(address(p), anchor), { tag: old(a.tag) });
    have b.tag == old(a.tag) by normalize();
}
void choose(int32* p, int32* q, int32* anchor, int32 flag) {
    consumes c: cursor(address(p), anchor);
    produces *anchor;
} by {
    execute_until(loop(0));
    loop {
        owns c: cursor(address(cur), anchor);
        decreases 0;
        preserve by {
            if address(p) == address(q) {
                unfold(c);
                step(); step();
                let d = fold(cursor(address(p), anchor), { tag: 0 });
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
