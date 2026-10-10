# User tactic match refutation

A helper may refute an impossible constructor arm. Generated return and postcondition checks must run only on the surviving arm.

```c filename=user_tactic_match_refutes_impossible_arm.c
void user(int32 *p) {}
```

```click
verifying "user_tactic_match_refutes_impossible_arm.c";
spec enum Model { Empty, Full }
resource cell(p: int32*) { field model: Model; owns *p; }
tactic keep(p: int32*) {
    consumes a: cell(p);
    requires a.model != Model::Empty;
    produces b: cell(p);
    ensures b.model == old(a.model);
} by {
    match a.model {
        Model::Empty => { contradiction(a.model == Model::Empty); },
        Model::Full => {
            unfold(a);
            let b = fold(cell(p), { model: Model::Full });
            have b.model == old(a.model);
        },
    }
}
void user(int32* p) {
    consumes a: cell(p);
    requires a.model != Model::Empty;
    produces b: cell(p);
    ensures b.model == old(a.model);
} by {
    let { b: b } = keep(p, { a: a });
    execute(); simp();
}
```

```expect
pass
```
