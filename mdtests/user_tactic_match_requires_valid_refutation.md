# User tactic match refutation

A terminal contradiction must still prove the negation of its fact. The helper has no premise excluding Empty.

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
        Model::Empty => { contradiction(a.model == Model::Empty); },
        Model::Full => {
            unfold(a);
            let b = fold(cell(p), { model: Model::Full });
            have b.model == old(a.model) by { simp(); }
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
fail: requires an exact fact and its negation in that arm
```
