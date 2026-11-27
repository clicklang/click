# A bridged constructor-arm refutation names its own source

The constructor is reachable, so the local attempt to prove `false` fails.
The diagnostic points to the closer inside the selected arm.

```c filename=peek.c
struct node { int32 shade; };

int32 peek(struct node* p) {
    return 0;
}
```

```click
verifying "peek.c";

spec enum Cell {
    Missing,
    Present(struct node*),
}

resource cell_at(p: struct node*) {
    field model: Cell;
    match model {
        Cell::Missing => { },
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
    have p == p by close();
    match x.model {
        Cell::Missing => {
        },
        Cell::Present(identity) => {
            have p == p by close();
            have false by close(); close();
        },
    }
}
```

```expect
fail: could not establish `false`
```
