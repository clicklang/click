# A produced instance that reuses a child's name reads its own fields

`x` first names the `cellA` child an unfold takes from `root`. After the
fold returns it, `step(mk(p2), {})` binds `x` again, to the `cellB` instance
`mk` produces. `cellB` declares `v` second, so `x.v` must read the second
field, which `mk` sets to 1.
Before, `x` kept the child's resource for the rest of the proof, and this
true claim was refused.

```c filename=a_produced_instance_reusing_a_child_name_reads_its_own_fields.c
void mk(int32* p);
void f(int32* q, int32* p2) { mk(p2); }
```

```click
verifying "a_produced_instance_reusing_a_child_name_reads_its_own_fields.c";

resource cellA(p: int32*) {
    field v: int32;
    owns p[0..1];
    fact p[0] == v;
}

resource cellB(p: int32*) {
    field w: int32;
    field v: int32;
    owns p[0..1];
    fact p[0] == v;
}

resource root(q: int32*) {
    field u: int32;
    owns k: cellA(q);
    fact k.v == u;
}

extern void mk(int32* p) {
    consumes p[0..1];
    produces first: cellB(p);
    ensures first.v == 1;
    ensures first.w == 42;
}

void f(int32* q, int32* p2) {
    owns r: root(q);
    consumes p2[0..1];
} by {
    let { k: x, u: ru } = unfold(r);
    let r = fold(root(q), { u: ru }, { k: x });
    let { first: x } = step(mk(p2), {});
    have x.v == 1 by { simp(); }
    step();
    simp();
}
```

```expect
pass
```
