# An unconditional arithmetic postcondition includes its definedness obligation

This was formerly a negative fixture: lowering silently guarded the
callee's equality by the sum's domain. Structural lowering now makes the
callee prove that domain as part of establishing its unconditional
postcondition. Its body returns zero, so the obligation holds for every
entry value. The caller receives both the equality and its definedness and
can prove monotonicity from the nonnegative result.

The explicitly guarded counterpart remains negative in
[`explicit_guarded_postcondition_unbounded_stays_guarded.md`](explicit_guarded_postcondition_unbounded_stays_guarded.md).

```c filename=guarded_postcondition_unbounded_stays_guarded.c
struct box {
    int v;
};

int pick(struct box* b) {
    return 0;
}

int caller(struct box* b) {
    int got;
    got = pick(b);
    return got;
}
```

```click
resource counted(b: struct box*) {
    field live: int32;
    owns *b;
    fact 0 <= live;
}

verifying "guarded_postcondition_unbounded_stays_guarded.c";

int32 pick(struct box* b) {
    owns st: counted(b);
    ensures 0 <= result;
    ensures to_integer(st.live) == to_integer(old(st.live) + result);
} by {
    let { live: n } = unfold(st);
    let st = fold(counted(b), { live: n });
}

int32 caller(struct box* b) {
    owns st: counted(b);
    ensures old(st.live) <= st.live;
} by {
    step();
    step(pick, { st: st });
}
```

```expect
pass
```
