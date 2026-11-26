# A function-level `match` arm closes after unfolding an impossible resource

The `Cell::Missing` arm of `peek` is impossible because the function requires
`p != 0` and the arm's body says `p == 0`. That body is folded in the
instance. Unfolding in the arm publishes `p == 0`, so the opposite facts
establish `false`. Then `close()` ends the execution path at the current
point. An arm can also establish its refutation through a `have`. See
[`function_match_arm_closes_by_contradiction_after_a_have.md`](function_match_arm_closes_by_contradiction_after_a_have.md).

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
    requires p != 0;
    ensures result == 0;
} by {
    match x.model {
        Cell::Missing => {
            unfold(x);
            close();
        },
        Cell::Present(identity) => {
            step_until(function.exit);
            close();
        },
    }
}
```

```expect
pass
```
