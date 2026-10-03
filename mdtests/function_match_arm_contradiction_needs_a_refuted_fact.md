# A function-level `match` arm's `contradiction` must name a refuted fact

The arm of
[`function_match_arm_closes_by_contradiction_after_an_unfold.md`](function_match_arm_closes_by_contradiction_after_an_unfold.md),
except that the function no longer requires `p != 0`. Unfolding the
`Cell::Missing` body still publishes `p == 0`, but nothing on the arm's path
denies it, so the arm is not impossible and its `contradiction` is refused,
naming the proposition as written.

```c filename=peek_nonnull.c
struct node { int32 shade; };

int32 peek(struct node* p) {
    return 0;
}
```

```click
verifying "peek_nonnull.c";

spec enum Cell {
    Missing,
    Present(struct node*),
}

resource cell_at(p: struct node*) {
    field model: Cell;
    match model {
        Cell::Missing => { fact p == 0; },
        Cell::Present(identity) => {
            owns identity->shade;
            fact p == identity;
        },
    }
}

int32 peek(struct node* p) {
    owns x: cell_at(p);
    ensures result == 0;
} by {
    match x.model {
        Cell::Missing => {
            unfold(x);
            contradiction(p == 0);
        },
        Cell::Present(identity) => {
            execute();
            simp();
        },
    }
}
```

```expect
fail: constructor-arm `contradiction(p == 0)` requires an exact fact and its negation in that arm
```
