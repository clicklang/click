# a call step's binder map selects an inline helper's contract

A `static inline` helper with a verified contract is called through that
contract, like any other function. A call step's binder map,
`step(fill(p), { x: x })`, is how a proof selects a callee contract's instance
binders, and on such a helper it selects the helper's `consumes x` exactly as
it would for an ordinary function. The call carries the helper's
translation-unit-local execution name `fill#inline:…`, and the step still
matches it by the spelling the proof wrote.

A helper with no contract still runs its body at the call site, so a binder
map on it binds nothing and is refused
([`call_step_binder_map_on_an_uncontracted_inline_helper_rejected.md`](call_step_binder_map_on_an_uncontracted_inline_helper_rejected.md)).

```c filename=call_step_binder_map_selects_an_inline_helpers_contract.c
struct cell { unsigned long word; };

static inline __attribute__((always_inline)) void fill(struct cell *p) {
    p->word = 1;
}

void caller(struct cell *p) {
    fill(p);
}
```

```click
verifying "call_step_binder_map_selects_an_inline_helpers_contract.c";

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
    step();
    simp();
}
```

```expect
pass
```
