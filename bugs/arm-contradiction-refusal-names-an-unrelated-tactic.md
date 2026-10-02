# A refused arm `contradiction` is reported at an unrelated earlier tactic

## Violated invariant

A proof error names the tactic that failed. When an arm of a function-level proof `match` ends in a `contradiction` that is not justified, the refusal is correct but it is attributed to a tactic outside the `match`: the source excerpt and the `tactic@LINE` label point at whichever `have` precedes the `match`, which verified.

In a large proof this sends the reader to the wrong place. While writing the `rb_next` proof the same message pointed at a `have` more than a hundred lines above the arm that owned the `contradiction`, and the only way to find the arm was to bisect.

## Reproduction

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
    have p == p by { normalize(); }
    match x.model {
        Cell::Missing => {
            execute();
            simp();
        },
        Cell::Present(identity) => {
            contradiction(x.model == Cell::Present(identity));
        },
    }
}
```

`click verify` on this as an mdtest reports, with the `have` on line 34 and the `contradiction` on line 41:

```
proof error:
  constructor-arm `contradiction` requires an exact fact and its negation in that arm

tactic@34:
  have p == p by { normalize(); }
```

The refusal itself is right: nothing denies `Cell::Present`. The location is wrong.

## Intended regression

Add the sidecar above as an mdtest whose `expect fail` substring includes the `contradiction` tactic's own text, so the fixture fails while the excerpt shows the `have`.

## Acceptance criteria

- The error's `tactic@` label and excerpt are the `contradiction` that was refused, and the message says which arm it stands in.
- The same holds when the `match` is nested in another arm or follows a loop.
- No change to which proofs are accepted; `scripts/check.sh` passes.
