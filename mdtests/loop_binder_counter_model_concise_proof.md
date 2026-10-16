# a loop binder's model proof closes its invariants without a certificate

This checks the unexpanded `bump_n` proof: the body states `c.count == i`
before the increment, refolds `counter(p)` with the new model, and lets
`close_invariants()` discharge the bundle at the back edge.

```c filename=loop_binder_counter_model_concise_proof.c
struct cell { int32 value; };

void bump_n(struct cell* p, int32 n) {
    int32 i;
    i = 0;
    while (i < n) {
        p->value = p->value + 1;
        i = i + 1;
    }
}
```

```click
verifying "loop_binder_counter_model_concise_proof.c";

resource counter(p: struct cell*) {
    field count: int32;
    owns p->value;
    fact p->value == count;
}

void bump_n(struct cell* p, int32 n) {
    requires n >= 0;
    requires n <= 1000;
    owns c: counter(p);
    requires c.count == 0;
    ensures c.count == old(c.count) + n;
} by {
    step();
    step();
    loop {
        decreases n - i;
        owns c: counter(p);
        invariant i >= 0;
        invariant i <= n;
        invariant c.count == old(c.count) + i;

        initialize by simp();
        preserve by {
            have c.count == i by { simp() using { c.count == old(c.count) + i; old(c.count) == 0; } }
            unfold(c);
            step();
            step();
            let c = fold(counter(p), { count: old(c.count) + i });
            close_invariants();
        }
    }
    have i == n by simp();
    execute();
    simp();
}
```

```expect
pass
```
