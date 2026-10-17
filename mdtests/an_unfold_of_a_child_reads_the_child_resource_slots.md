# An unfold of a child reads the child's resource's slots

`top` has a scalar field `x`, and its child `mid` has a child slot `x`.
`let { x: k } = unfold(m)` opens `m`, a `mid`, so `x` there is `mid`'s slot
and `k` is a `cell`. Before, the parser recorded `m` under its parent's
resource, `top`, and read `x` as `top`'s scalar field: `k` became a field
value, and the unfold of `k` was refused.

```c filename=child_slot_named_like_a_grandparent_field.c
int32 get(int32* p) { return *p; }
```

```click
verifying "child_slot_named_like_a_grandparent_field.c";

resource cell(p: int32*) {
    field v: int32;
    owns p[0..1];
    fact p[0] == v;
}

resource mid(p: int32*) {
    field w: int32;
    owns x: cell(p);
    fact x.v == w;
}

resource top(p: int32*) {
    field x: int32;
    owns c: mid(p);
    fact c.w == x;
}

int32 get(int32* p) {
    owns t: top(p);
    ensures result == t.x;
} by {
    let { c: m, x: tx } = unfold(t);
    let { x: k } = unfold(m);
    let { v: kv } = unfold(k);
    execute();
    let k = fold(cell(p), { v: kv });
    let m = fold(mid(p), { w: k.v }, { x: k });
    let t = fold(top(p), { x: tx }, { c: m });
    simp();
}
```

```expect
pass
```
