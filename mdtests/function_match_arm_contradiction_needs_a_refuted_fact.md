# A reachable constructor arm cannot prove false

Unfolding the missing-cell arm gives `p == 0`. Without a conflicting requirement, the arm cannot establish `false`.

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
            have false by close(); close();
        },
        Cell::Present(identity) => {
        },
    }
}
```

```expect
fail: could not establish `false`
```
