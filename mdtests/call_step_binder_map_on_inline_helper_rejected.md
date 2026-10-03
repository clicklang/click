# a call step's binder map cannot select an inline helper's contract

A `static inline` helper has no contract boundary: every call executes its
checked body at the call site, on the caller's own resources, and a sidecar
contract that names the helper is checked against that body but never applied
in its place. A call step's binder map, `step(f(p), { x: x })`, is how a proof
selects a callee contract's instance binders, so on an inline helper it would
bind nothing. The step is refused for that reason, naming it.

The helper's own contract verifies, so the refusal is about the caller's step
and not about the helper. Before, the step was refused as if the frontier held
no call to `fill` at all, because the call carries the helper's
translation-unit-local execution name `fill#inline:…` rather than the spelling
the proof wrote.

```c filename=call_step_binder_map_on_inline_helper_rejected.c
struct cell { unsigned long word; };

static inline __attribute__((always_inline)) void fill(struct cell *p) {
    p->word = 1;
}

void caller(struct cell *p) {
    fill(p);
}
```

```click
verifying "call_step_binder_map_on_inline_helper_rejected.c";

resource filled(p: struct cell*) {
    field tag: int32;
    owns p->word;
}

void fill(struct cell* p) {
    consumes x: filled(p);
    produces y: filled(p);
} by {
    unfold(x);
    execute();
    let y = fold(filled(p), { tag: 0 });
    simp();
}

void caller(struct cell* p) {
    consumes x: filled(p);
    produces y: filled(p);
} by {
    let y = step(fill(p), { x: x });
    simp();
}
```

```expect
fail: a binder map cannot select a `static inline` helper's contract
```
