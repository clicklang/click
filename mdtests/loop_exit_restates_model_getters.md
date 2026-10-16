# Loop exits restate model getters using the successor model

The break path returns a freshly named model from a checked tactic. Its
getter fact must be available on the joined resource after the loop.
The C loop and break are unchanged.

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
    requires n > 0;
    requires state.model == Walk::Active;
    ensures pending(state.model) == 0;
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
    execute(); simp();
}
```

```expect
pass
```
