# a counting invariant survives the store that changes the count

`sweep` marks every cell of `visited[0..n]`. Its termination is the ordinary
`decreases n - i`; the counting content is the invariant
`unmarked(visited, 0, i) == 0`, that everything below the cursor is marked.

Two steps of the body need memory reasoning the proof does not spell out.
Appending the written cell reads it out of the state the store produced, so
the append law's last cell is the value that store wrote. Carrying the
invariant past the cursor's own `i++` needs the array argument `unmarked`
folds over to name the same state on both sides of a step that writes only
a local, which is what a block epoch gives it.

The prefix is preserved by ordinary proof steps. For each `k < i`,
`separate_elements` separates `visited[k]` from the endpoint store, and
`preserve` establishes its equality with the iteration-entry read. The existing
`unmarked_frame` lemma turns these cell equalities into equality of the prefix
counts. Rewriting then reuses the entry invariant. The enlarged prefix after
`i++` still needs the fold's append law, which `unfold` opens. The omitted-proof
companion remains `sweep_prefix_survives_its_endpoint_store_by_solve.md`.

```c filename=sweep_maintains_a_zero_unmarked_count.c
void sweep(int32 visited[], int32 n) {
    for (int32 i = 0; i < n; i++) {
        visited[i] = 1;
    }
}
```

```click
verifying "sweep_maintains_a_zero_unmarked_count.c";

import "unmarked_count_lemmas.click";

void sweep(int32 visited[], int32 n) {
    requires 0 <= n;
    requires n <= 1073741823;
    owns visited[0..n];
} by {
    step();
    step();
    have 0 <= 0;
    have unmarked(visited, 0, 0) == 0 by {
        unfold(unmarked(visited, 0, 0));
        normalize();
    }
    loop {
        decreases n - i;
        invariant 0 <= i;
        invariant i <= n;
        invariant unmarked(visited, 0, i) == 0;
        owns visited[0..n];
        initialize by { solve(); }
        preserve by {
            mark iter;
            have i < 2147483647 by {
                solve() using { i < n; n <= 1073741823; };
            }
            have viewable(visited[0..n]) by { observe(visited[0..n]); known(); }
            step();
            have unmarked(visited, 0, i) == 0 by {
                have forall (k: int32) {
                    0 <= k and k < i implies visited[k] == at(iter, visited[k])
                } by {
                    intro(); intro();
                    have k < n by { solve() using { k < i; i < n; }; }
                    have i != k by { solve() using { k < i; }; }
                    have separate(memory(visited[i]), memory(visited[k])) by {
                        apply(click::separation::separate_elements(visited, i, k)) using { i != k; };
                    }
                    have separate(loop(0).statement(0).footprint, memory(visited[k])) by {
                        normalize() using { separate(memory(visited[i]), memory(visited[k])); };
                    }
                    preserve(memory(visited[k]), loop(0).statement(0));
                }
                have viewable(visited[0..n]) by { observe(visited[0..n]); known(); }
                have 0 <= 0 by { normalize(); }
                have i <= i by { normalize(); }
                apply(unmarked_frame(visited, at(iter, visited), 0, n, i, i)) using {
                    0 <= 0;
                    0 <= i;
                    i <= i;
                    i <= n;
                    n <= 1073741823;
                    viewable(visited[0..n]);
                    at(iter, viewable(visited[0..n]));
                    forall (k: int32) { 0 <= k and k < i implies visited[k] == at(iter, visited[k]) };
                };
                rewrite(unmarked(visited, 0, i), unmarked(at(iter, visited), 0, i));
                known();
            }
            have unmarked(visited, 0, i + 1) == 0 by {
                unfold(unmarked(visited, 0, i + 1));
                solve();
            }
            step();
        }
    }
}
```

```expect
pass
```
