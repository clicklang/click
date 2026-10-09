# Loop exit resource arguments

Each exit hands back cursor(cur, anchor), but cur differs between exits. The loop join must keep the declared resource argument tied to the joined local so it can be passed to a helper.

```c filename=loop_exit_resource_argument_tracks_current_local.c
void choose(int32 *p, int32 *q, int32 *anchor, int32 flag) {
    int32 *cur = p;
    while (1) {
        if (flag) { cur = q; break; }
        else { break; }
    }
}
```

```click
verifying "loop_exit_resource_argument_tracks_current_local.c";
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
    let { b: b } = keep(cur, anchor, { a: c });
    unfold(b);
    execute(); simp();
}
```

```expect
pass
```
