# A model pointer binding does not preserve a changed cell

Resolving an equal proof pointer supplies no frame evidence for a cell
that the C loop actually writes. Both alias and source are explicitly cited.

```c filename=transport_loop_alias.c
int32 update(int32 *p) {
    while (1) { p[0] = 9; break; }
    return p[0];
}
```
```click
verifying "transport_loop_alias.c";
spec enum View { At(int32*) }
resource first(p: int32*) {
    field model: View;
    match model {
        View::At(alias) => {
            owns p[0..2];
            fact p == alias;
            fact p[0] == 7;
        },
    }
}
int32 update(int32* p) {
    owns state: first(p);
    ensures result == 7;
} by {
    match state.model {
        View::At(alias) => {
            loop {
                owns state: first(p);
                decreases 0;
                invariant state.model == old(state.model);
                invariant state.model == View::At(alias);
                initialize by simp;
                preserve by {
                    unfold(state);
                    step();
                    transport(at(statement(0).entry, p[0]) == 7, alias[0] == 7) using {
                        at(statement(0).entry, p[0]) == 7;
                        p == alias;
                    };
                    let state = fold(first(p), {model: View::At(alias)});
                    step();
                }
            }
            unfold(state); execute();
            let state = fold(first(p), {model: View::At(alias)});
            simp();
        },
    }
}
```
```expect
fail: `transport using` found no frame evidence
```
