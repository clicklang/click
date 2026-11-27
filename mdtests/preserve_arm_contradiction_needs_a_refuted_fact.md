# A reachable preservation arm cannot prove false

The loop-body arm can restate `n >= 0` but has no evidence that the path is impossible. Its attempted proof of `false` fails.

```c filename=preserve_arm_contradiction_needs_a_refuted_fact.c
struct cell {
    int32 value;
    struct cell* next;
};

void bump_n(struct cell *node, int32 n) {
    int32 i;
    i = 0;
    while (i < n) {
        node->value = 7;
        i = i + 1;
    }
}
```

```click
verifying "preserve_arm_contradiction_needs_a_refuted_fact.c";

spec enum CellList {
    Nil,
    Cons(struct cell*, int32, CellList),
}

resource list_at(p: struct cell*) {
    field model: CellList;
    match model {
        CellList::Nil => { fact p == 0; },
        CellList::Cons(identity, value, tail_model) => {
            owns p->value;
            owns p->next;
            owns tail: list_at(p->next);
            fact p != 0;
            fact p == identity;
            fact p->value == value;
            fact tail.model == tail_model;
        },
    }
}

void bump_n(struct cell* node, int32 n) {
    requires n >= 0;
    requires n <= 1000;
    requires node != 0;
    owns l: list_at(node);
    requires l.model != CellList::Nil;
} by {
    step();
    step();
    loop {
        owns l: list_at(node);
        decreases to_integer(n) - to_integer(i);
        invariant i >= 0;
        invariant i <= n;
        invariant node != 0;

        initialize by close();
        maintain by {
            match l.model {
                CellList::Nil => { close(); },
                CellList::Cons(identity, value, tail_model) => {
                    have n >= 0;
                    have false by close();
                    let { tail: t } = unfold(l);
                    step();
                    step();
                    let l = fold(list_at(node), {
                        model: CellList::Cons(identity, 7, tail_model),
                        tail: t
                    });
                },
            }
        }
    }
}
```

```expect
fail: could not establish `false`
```
