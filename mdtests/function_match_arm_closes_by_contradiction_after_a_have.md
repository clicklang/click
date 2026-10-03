# A function-level `match` arm closes by `contradiction` after a `have`

`peek` holds a modelled instance and matches its model. The `Cell::Missing` arm
is impossible, and the proof says why in three steps: the precondition restated
at the arm's constructor, the predicate's value there, and the `contradiction`
between them.

A `contradiction` refutes the path it stands on wherever on that path it
stands, inside a loop's `preserve`
([`preserve_arm_contradiction_after_a_have.md`](preserve_arm_contradiction_after_a_have.md))
and in a `match` at the function's own level. An arm that only bridges facts
before its `contradiction` (`have`s, unfolds, theorem applications, but no C
step) runs that bridge inside the arm, and the arm is then excluded from the
facts the bridge reached, exactly as a sole `contradiction` excludes it. It
owes no C outcome and does not reach function exit.

Here the sole-tactic form `contradiction(x.model == Cell::Missing)` happens to
work too, because the predicate is a precondition and contract lowering refutes
the arm from it. The bridged form is the only one there is when the refuting
fact is established by the proof rather than required by the contract, as
after the unchanged Linux `rb_next`'s ascent loop, where what rules out a
`Right` frame is something each `break` exit stated ([`rb_next.md`](rb_next.md)).
The bridge may also be an `unfold`
([`function_match_arm_closes_by_contradiction_after_an_unfold.md`](function_match_arm_closes_by_contradiction_after_an_unfold.md)),
and a `contradiction` the arm does not refute is still refused
([`function_match_arm_contradiction_needs_a_refuted_fact.md`](function_match_arm_contradiction_needs_a_refuted_fact.md)).

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
pass
```
