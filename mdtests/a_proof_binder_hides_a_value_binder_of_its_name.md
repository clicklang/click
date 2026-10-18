# A proof binder hides a value binder of its name

The contract's value binder `s: seg(p, _)` has the parameter `s.n`, which
is 5. The unfold binds `s` again, to `root`'s `cellA` child, so until the
block ends `s.n` reads that child's field, which is 7, as `s` alone names
the child. Before, `s.n` still read the value binder's parameter while `s`
named the child.

```c filename=a_proof_binder_hides_a_value_binder_of_i.c
void f(int32* p, int32* q) { }
```

```click
verifying "a_proof_binder_hides_a_value_binder_of_i.c";

resource seg(p: int32*, n: int32) {
    owns p[0..1];
    fact p[0] == n;
}

resource cellA(p: int32*) {
    field n: int32;
    owns p[0..1];
    fact p[0] == n;
}

resource root(q: int32*) {
    field u: int32;
    owns left: cellA(q);
    fact left.n == u;
}

void f(int32* p, int32* q) {
    owns s: seg(p, _);
    owns r: root(q);
    requires s.n == 5;
    requires r.u == 7;
} by {
    let { left: s, u: ru } = unfold(r);
    have s.n == 7 by { simp(); }
    let r = fold(root(q), { u: ru }, { left: s });
    execute();
    simp();
}
```

```expect
pass
```
