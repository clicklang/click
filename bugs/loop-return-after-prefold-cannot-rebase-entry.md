# A return from a loop cannot certify after a preceding resource fold

A checked resource fold before a loop must not prevent certification of a
function whose loop returns. The following true claim passes its proof steps,
then fails contract certification with `the checked execution of walk started
at a different entry state than the contract and could not be rebased onto it`.
The caller-owned marker is untouched. The C is fixed.

## Reproduction

Save this fixture and run `click verify` on it:

# A return inside a loop exports the exchanged resources and caller frame
```c filename=walk.c
struct Node { struct Node *next; };
struct Node *walk(struct Node *p, int *marker) {
    do { p = p->next; return p; } while (p);
    return p;
}
```
```click
verifying "walk.c";
spec enum Chain { Empty, Node(struct Node*, Chain), }
spec enum Path { Top, Step(struct Node*, Path), }
resource list(p: struct Node*) {
    field model: Chain;
    match model {
        Chain::Empty => { fact p == 0; },
        Chain::Node(identity, rest) => {
            owns p->next;
            owns tail: list(p->next);
            fact p != 0;
            fact p == identity;
            fact tail.model == rest;
        },
    }
}
resource path(p: struct Node*) {
    field model: Path;
    match model {
        Path::Top => { },
        Path::Step(identity, before) => {
            owns identity->next;
            owns up: path(identity);
            fact identity != 0;
            fact identity->next == p;
            fact up.model == before;
        },
    }
}
struct Node* walk(struct Node* p, int32* marker) {
    consumes t: list(p);
    owns marker[0];
    requires p != 0;
    requires marker[0] == 9;
    ensures marker[0] == 9;
} by {
    let c = fold(path(p), { model: Path::Top });
    loop {
        owns t: list(p);
        owns c: path(p);
        decreases t;
        invariant p != 0;
        initialize by simp;
        preserve by {
            match t.model {
                Chain::Empty => { unfold(t); contradiction(p == 0); },
                Chain::Node(identity, rest) => {
                    let { tail: remaining } = unfold(t);
                    let whole = fold(path(p->next), { model: Path::Step(identity, c.model) }, { up: c });
                    step();
                    step();
                },
            }
        }
    }
    simp();
}
```
```expect
pass
```

## Reduction and acceptance

Moving only the initial empty `path(p)` fold into the preservation proof and
removing `owns c: path(p)` from the loop makes the claim verify. A stronger
passing regression, `mdtests/do_while_return_restores_changed_resource_frame.md`,
also returns the reconstructed path and remaining list in named `produces`
clauses. This distinguishes the entry-rebase failure from exit frame loss.

Preserve the checked pre-loop fold transition when certifying the loop's
returned path. Do not discard entry resources or accept an arbitrary changed
entry state. The reproduction must verify and pass expansion audit; entry
rebase regressions that reject changed memory or population state must still
fail. Nested return paths must retain their enclosing resource transitions.
