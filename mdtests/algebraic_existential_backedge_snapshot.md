# An algebraic witness closes across a disjoint store

The body rebuilds the invariant after writing `visited`. The loop closer must
check that same array-dependent proposition at the back edge.

```c filename=algebraic_existential_backedge_snapshot.c
void traverse(int32 *next, int32 *visited) {
    int32 cur = 0;
    while (visited[cur] == 0) {
        visited[cur] = 1;
        cur = next[cur];
    }
}
```

```click
verifying "algebraic_existential_backedge_snapshot.c";

function walk(next: int32[], from: int32, fuel: Nat) -> int32 decreases fuel {
    match fuel {
        Nat::Zero => from,
        Nat::Succ(previous) => next[walk(next, from, previous)],
    }
}

void traverse(int32 *next, int32 *visited) diverges {
    views next[0..1];
    owns visited[0..1];
    requires separate(memory(next[0..1]), memory(visited[0..1]));
    requires next[0] == 0;
} by {
    step();
    step();
    loop diverges {
        invariant cur == 0;
        invariant next[0] == 0;
        invariant exists (fuel: Nat) { walk(next, 0, fuel) == cur };
        views next[0..1];
        owns visited[0..1];
        initialize by {
            have cur == 0;
            have next[0] == 0;
            have exists (fuel: Nat) { walk(next, 0, fuel) == cur } by {
                witness { fuel: Nat::Zero };
                unfold(walk(next, 0, Nat::Zero));
            }
            solve();
        }
        preserve by {
            mark before_visit;
            step();
            transport(at(before_visit, next[0]) == 0, next[0] == 0) using {
                at(before_visit, next[0]) == 0;
                at(before_visit, cur) == 0;
                separate(memory(next[0..1]), memory(visited[0..1]));
            };
            step();
            have exists (fuel: Nat) { walk(next, 0, fuel) == cur } by {
                witness { fuel: Nat::Succ(Nat::Zero) };
                unfold(walk(next, 0, Nat::Zero));
                unfold(walk(next, 0, Nat::Succ(Nat::Zero)));
                solve();
            }
            close_invariants();
        }
    }
}
```

```expect
pass
```
