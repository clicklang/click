# Preservation uses an in-scope model pointer

A model-match pointer names the same owned cells as the C argument.
Explicit preservation carries the iteration-entry fact across the store;
rewriting then identifies the model pointer with the C argument.

```c filename=transport_loop_alias.c
int32 update(int32 *p) {
    while (1) { p[1] = 9; break; }
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
                initialize by solve();
                maintain by {
                    unfold(state);
                    mark iteration;
                    have p[0] == 7 by { known(); }
                    have p == alias by { solve(); }
                    have separate(memory(p[1]), memory(p[0])) by {
                        apply(click::separation::separate_elements(p, 1, 0));
                    }
                    step();
                    have separate(statement(0).statement(0).footprint, memory(p[0])) by {
                        close() using { separate(memory(p[1]), memory(p[0])); };
                    }
                    have p[0] == at(iteration, p[0]) by {
                        preserve(memory(p[0]), statement(0).statement(0));
                    }
                    have p[0] == 7 by { rewrite(p[0], at(iteration, p[0])); known(); }
                    have alias[0] == 7 by { rewrite(alias, p); known(); }
                    let state = fold(first(p), {model: View::At(alias)});
                    step();
                }
            }
            unfold(state); step_until(function.exit);
            let state = fold(first(p), {model: View::At(alias)});
            solve();
        },
    }
}
```
```expect
pass
```
