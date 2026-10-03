# A function-level `match` arm closes by `contradiction` after an `unfold`

The `Cell::Missing` arm of `peek` is impossible because the function requires
`p != 0` and the arm's body says `p == 0`. That body is folded in the
instance, so the arm first unfolds it, which publishes `p == 0`, and then
refutes itself. The `unfold` runs inside the arm and the arm is excluded from
the facts it reached; see
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
pass
```
