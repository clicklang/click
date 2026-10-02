# A function-level `match` arm cannot close by `contradiction` after a `have`

`peek` holds a modelled instance and matches its model. The `Cell::Missing` arm
is impossible, and the proof says why in three steps: the precondition restated
at the arm's constructor, the predicate's value there, and the `contradiction`
between them.

Inside a loop's `preserve` this shape is supported: a `contradiction` refutes
the path it stands on wherever on that path it stands
([`preserve_arm_contradiction_after_a_have.md`](preserve_arm_contradiction_after_a_have.md)).
In a `match` at the function's own level it is not. An arm is accepted there
only when `contradiction` is its sole tactic, which needs the refuted fact and
its exact negation to be available with no bridging step; with the bridge the
proof is declined as a shape the verifier cannot yet certify, although every
tactic in it is valid.

Here the sole-tactic form `contradiction(x.model == Cell::Missing)` happens to
work, because the predicate is a precondition and contract lowering refutes the
arm from it. The fixture keeps the bridged form because that is the only one
there is when the refuting fact is established by the proof rather than
required by the contract. The unchanged Linux `rb_next` needs it after its
ascent loop, where what rules out a `Right` frame is something each `break`
exit stated ([`rb_next.md`](rb_next.md)). The fixture pins the refusal; it
becomes a positive when a function-level arm may close where its
`contradiction` stands.

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
                rewrite(Cell::Missing == x.model);
                assumption();
            }
            have is_present(Cell::Missing) != 0 by {
                rewrite(is_present(Cell::Missing) == 1);
                normalize();
            }
            have is_present(Cell::Missing) == 0 by {
                unfold(is_present(Cell::Missing));
                normalize();
            }
            contradiction(is_present(Cell::Missing) == 0);
        },
        Cell::Present(identity) => {
            execute();
            simp();
        },
    }
}
```

```expect
fail: which is not implemented in this execution context
```
