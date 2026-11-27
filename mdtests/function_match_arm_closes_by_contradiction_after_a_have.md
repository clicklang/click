# A match arm closes after a bridge establishes false

The bridge records the opposing fact in the constructor arm. The arm then
uses `close()` to exclude that constructor before executing C.

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

function is_present(cell: Cell) -> int32 {
    match cell {
        Cell::Missing => 0,
        Cell::Present(identity) => 1,
    }
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
    requires is_present(x.model) == 1;
    ensures result == 0;
} by {
    match x.model {
        Cell::Missing => {
            have is_present(Cell::Missing) == 1 by {
                rewrite(Cell::Missing, x.model);
                close();
            }
            have is_present(Cell::Missing) != 0 by {
                rewrite(is_present(Cell::Missing), 1);
                close();
            }
            have is_present(Cell::Missing) == 0 by {
                unfold(is_present(Cell::Missing));
                close();
            }
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
