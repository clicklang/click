# A loop exit proof can use a model getter without spelling body-local names

An explicit split on the unchanged guard tells the proof how the loop will
exit. The break proof uses the rebound model getter. The false-guard proof
uses the value of `n`.

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
        rewrite(done.model, Walk::Done); unfold(pending(Walk::Done)); known();
    }
}
void walk(int32 n) {
    owns state: ghost(0);
    requires n >= 0;
    requires state.model == Walk::Active;
    ensures n == 0 or pending(state.model) == 0;
} by {
    if n > 0 {
        loop {
            owns state: ghost(0);
            decreases n;
            invariant n > 0;
            invariant state.model == Walk::Active;
            initialize by solve();
            maintain by {
                let { done: state } = stop({ dirty: state });
                have pending(state.model) == 0 by known();
                step();
            }
        }
        step();
        have pending(state.model) == 0 by known();
        solve();
    } else {
        have n == 0 by solve();
        step_until(function.exit);
        solve();
    }
}
```

```expect
pass
```
