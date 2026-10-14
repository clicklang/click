# a loop-body proof `match` closes its invariants without a certificate

This checks the unexpanded proof `match` inside `preserve`: the excluded arm
closes by `contradiction`, and the live arm relates its binding to the entry
model, refolds the binder, and closes the invariants with `close_invariants()`.

```c filename=loop_body_proof_match_concise_proof.c
struct cell { int32 value; };

int32 spin(struct cell *node, int32 n) {
    int32 i;
    i = 0;
    while (i < n) {
        i = i + 1;
    }
    return node->value;
}
```

```click
verifying "loop_body_proof_match_concise_proof.c";

spec enum Maybe { None, Some(int32) }

resource cell(p: struct cell*) {
    field model: Maybe;
    match model {
        Maybe::None => { fact p == 0; },
        Maybe::Some(value) => { owns p->value; fact p->value == value; },
    }
}

int32 spin(struct cell* node, int32 n) {
    requires n >= 0;
    requires node != 0;
    owns c: cell(node);
    requires c.model != Maybe::None;
    ensures c.model == old(c.model);
} by {
    step();
    step();
    loop {
        decreases n - i;
        owns c: cell(node);
        invariant i >= 0;
        invariant i <= n;
        invariant c.model == old(c.model);
        invariant c.model != Maybe::None;

        initialize by simp;
        preserve by {
            match c.model {
                Maybe::None => { contradiction(c.model == Maybe::None); },
                Maybe::Some(value) => {
                    have Maybe::Some(value) == old(c.model) by {
                        simp() using { c.model == Maybe::Some(value); c.model == old(c.model); }
                    }
                    unfold(c);
                    step();
                    let c = fold(cell(node), { model: Maybe::Some(value) });
                    close_invariants();
                },
            }
        }
    }
    step();
    simp();
}
```

```expect
pass
```
