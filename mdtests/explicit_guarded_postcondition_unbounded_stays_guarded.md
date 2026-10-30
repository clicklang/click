# An explicitly guarded postcondition does not establish its domain

The callee promises the equality only when its sum is defined. With no
upper bounds at the call, the caller cannot discard that explicit guard
and infer monotonicity.

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
    ensures defined(old(st.live) + result) implies to_integer(st.live) == to_integer(old(st.live) + result);
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
fail: `ensures old(st.live) <= st.live` failed for `caller.ensures_0`
```
