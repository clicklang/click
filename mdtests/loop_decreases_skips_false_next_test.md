# A false next test needs no structural descent

The body retains the same resource and makes `i < n` false. Every continuing
edge would owe a strict descendant, but this body always exits at its next test.

```c filename=loop_decreases_skips_false_next_test.c
struct cell { int32 value; };

void spin(struct cell *node, int32 n) {
    int32 i;
    i = 0;
    while (i < n) {
        i = n;
    }
}
```

```click
verifying "loop_decreases_skips_false_next_test.c";

spec enum Maybe { None, Some(int32) }

resource cell(p: struct cell*) {
    field model: Maybe;
    match model {
        Maybe::None => { fact p == 0; },
        Maybe::Some(value) => { owns p->value; fact p->value == value; },
    }
}

void spin(struct cell* node, int32 n) {
    requires n >= 0;
    requires node != 0;
    owns c: cell(node);
    requires c.model == Maybe::Some(7);
    ensures c.model == old(c.model);
} by {
    step();
    step();
    loop {
        owns c: cell(node);
        decreases c;
        invariant i >= 0;
        invariant i <= n;
        invariant c.model == Maybe::Some(7);

        initialize by solve();
        preserve by {
            step();
        }
    }
    step();
    solve();
}
```

```expect
pass
```
