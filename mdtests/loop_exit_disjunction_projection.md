# A loop exit disjunction can be projected without spelling body-local names

The guard exit supplies the false guard; the break exit supplies the repaired
model getter. Discarded ownership history is not needed in the caller proof.

```c filename=program.c
void walk(int n) { while (n > 0) { break; } }
```

```click
verifying "program.c";
spec enum Walk { Active, Done }
function pending(w: Walk) -> int32 { match w { Walk::Active => 1, Walk::Done => 0, } }
resource ghost(id: int32) { field model: Walk; }
tactic stop() {
    consumes dirty: ghost(0);
    produces done: ghost(0);
    ensures pending(done.model) == 0;
} by {
    unfold(dirty);
    let done = fold(ghost(0), { model: Walk::Done });
    have pending(done.model) == 0 by {
        rewrite(done.model == Walk::Done); unfold(pending(Walk::Done)); normalize();
    }
}
void walk(int32 n) {
    owns state: ghost(0);
    requires n >= 0;
    requires state.model == Walk::Active;
    ensures n == 0 or pending(state.model) == 0;
} by {
    loop {
        owns state: ghost(0);
        decreases n;
        invariant n >= 0;
        invariant state.model == Walk::Active;
        initialize by simp();
        preserve by {
            let { done: state } = stop({ dirty: state });
            step();
        }
    }
    step();
    extract(not (n > 0) or pending(state.model) == 0);
    have n == 0 or pending(state.model) == 0 by {
        cases {
            not (n > 0) => {
                have n == 0 by { simp(); }
                assumption();
            }
            pending(state.model) == 0 => { assumption(); }
        }
    }
    simp();
}
```

```expect
pass
```
