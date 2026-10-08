# Do-while resource exits lose loop binders and the withheld caller frame

A loop that moves a cursor and refolds its resources can verify its body and
termination, but its guard-false exit does not preserve the ownership interface
promised by the loop's clauses. This blocks the unchanged Linux rbtree
successor-descent loop.

## Reproduction

Save the following as a Markdown fixture and run `click verify <file>.md`.
It should pass: the loop transfers the finite input chain into a path and never
touches `marker`; the caller still owns that cell when the loop ends.
Currently the final store is refused with `missing resource fact owns marker[0]`.

```c filename=walk.c
struct Node { struct Node *next; };
void walk(struct Node *p, int *marker) {
    do { p = p->next; } while (p);
    *marker = 7;
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
void walk(struct Node* p, int32* marker) {
    consumes t: list(p);
    owns marker[0];
    requires p != 0;
    ensures marker[0] == 7;
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
                    let { tail: next } = unfold(t);
                    let frame = fold(path(p->next), { model: Path::Step(identity, c.model) }, { up: c });
                    step();
                    if p == 0 {
                    } else {
                        close_invariants();
                    }
                },
            }
        }
    }
    execute(); simp();
}
```
```expect
pass
```

A second failure uses the same fixture without the marker parameter, its
ownership clause, or its store, with `ensures 1 == 1`. Before `execute()`, add:

```click
have c.model != Path::Top by { normalize(); }
```

This is true because a do-while executes at least once and every iteration folds
one `Path::Step`. Instead it is refused because the model field's resource
instance is not held. A `match c.model` fails the same way. The diagnostic is
attributed to the entire `loop`, rather than the post-loop field access.
Both failures reproduce in small fixtures; no rbtree imports are needed.

## Investigation

`CLoopHead::restored_exit_state` in `src/kernel/loops.rs` restores `top.resources`
only when the exit's resources equal the original body context. A real traversal
changes those resources, so the withheld caller frame is dropped. The surface
preservation driver's `CLoopFinalExitCandidate` also retains body-local instance
names, although the kernel's continuing-edge path rebinds loop instance names.

Rebinding the candidate alone makes the model readable, but does not restore
the caller frame. Resource refolding after that experimental change also needs
validation; it is not a complete fix. No experimental loop-kernel patch is
included with this report. The separate pure-pointer spelling regression found
while building the rbtree proof is fixed and has its own passing fixture.

## Acceptance criteria

- The fixture passes and the loop's final path/empty-chain ownership can be
  returned in explicit `produces` clauses with model postconditions.
- The caller frame remains available after guard-false and break exits; it
  remains unavailable for writes inside the loop unless declared there.
- Missing or incompatible resources are refused. Restoring the frame must not
  grant duplicated ownership or retain invalid borrowed views, support records,
  or stable-loan authority.
- Continuing edges still prove their invariant and strict structural decrease;
  exiting edges do not have to reestablish a head-only `p != 0` invariant.
- Ordinary verification and expansion/audit agree, including the existing
  do-while vacuous-exit rejection fixtures.
- Restore the checked resource changes without rescanning unrelated caller
  state per exit; add deterministic scaling coverage over several frame sizes.
