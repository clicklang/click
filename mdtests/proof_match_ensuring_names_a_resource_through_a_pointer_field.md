# An interface names a resource through a pointer read from memory

The cell is reached through `h->inner`, a pointer the proof reads from
memory, and the `match` names the cell it rejoins with the same way:
`owns c: cell(h->inner)`. Neither arm writes `h->inner`, so both arms and the
state they join in read the same pointer there, and the interface's fact
about `c.model` is checked against the cell at it.

What does not work yet is a pointer the two arms know differently, such as a
child link that is null in one arm and a node in the other: the state the
arms join in has no one pointer value to read. `examples/rbtree-insert` folds
the parent inside each arm and names the parent instead.

```c filename=proof_match_ensuring_names_a_resource_through_a_pointer_field.c
struct cell { int32 value; };
struct holder { struct cell *inner; };

int32 peek(struct holder *h, int32 x) {
    int32 a;
    a = 0;
    return a;
}
```

```click
verifying "proof_match_ensuring_names_a_resource_through_a_pointer_field.c";

spec enum Sign { Neg(int32), Pos(int32) }

resource cell(p: struct cell*) {
    field model: Sign;
    match model {
        Sign::Neg(value) => {
            owns p->value;
            fact p->value == value;
            fact value < 0;
        },
        Sign::Pos(value) => {
            owns p->value;
            fact p->value == value;
            fact value >= 0;
        },
    }
}

int32 peek(struct holder* h, int32 x) {
    requires h != 0;
    owns &h->inner;
    owns c: cell(h->inner);
    ensures result == 0;
} by {
    step();
    match c.model ensuring {
        owns c: cell(h->inner);
        fact c.model == old(c.model);
    } {
        Sign::Neg(value) => {
            have Sign::Neg(value) == old(c.model) by { simp(); }
            unfold(c);
            let c = fold(cell(h->inner), { model: Sign::Neg(value) });
            have c.model == old(c.model) by { simp(); }
        },
        Sign::Pos(value) => {
            have Sign::Pos(value) == old(c.model) by { simp(); }
            unfold(c);
            let c = fold(cell(h->inner), { model: Sign::Pos(value) });
            have c.model == old(c.model) by { simp(); }
        },
    }
    step();
    step();
    simp();
}
```

```expect
pass
```
