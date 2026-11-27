# A user tactic must prove a constructor arm is impossible

The tactic is checked against its own preconditions. A caller’s stronger requirement cannot prove `false` in the tactic’s reachable constructor arm.

```c filename=user_tactic_match_requires_valid_refutation.c
void user(int32 *p) {}
```

```click
verifying "user_tactic_match_requires_valid_refutation.c";
spec enum Model { Empty, Full }
resource cell(p: int32*) { field model: Model; owns *p; }
tactic keep(p: int32*) {
    consumes a: cell(p);
    produces b: cell(p);
    ensures b.model == old(a.model);
} by {
    match a.model {
        Model::Empty => { have false by close(); close(); },
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
}
```

```expect
fail: could not establish `false`
```
