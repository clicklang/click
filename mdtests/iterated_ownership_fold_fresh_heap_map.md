# Iterated ownership: fold the whole clause over a freshly allocated guard map

The C loop initializes an occupancy map. Its quantified value invariant lets
whole-clause `fold` decide the logical guard for every index and rearrange the owned
resources. Folding the clause does not execute a C read or publish initialization
facts. A subsequent C load still needs independent validity evidence.

```c filename=iterated_ownership_fold_fresh_heap_map.c
void with_fresh_map(int32* data, int32 capacity) {
    int32* occupied;
    int32 i;

    occupied = malloc(capacity * 4);
    if (occupied == 0) {
        return;
    }
    i = 0;
    while (i < capacity) {
        occupied[i] = 0;
        i = i + 1;
    }
    free(occupied);
}
```

```click
import click::separation;

resource arena_cells(data: int32*, occupied: int32*, capacity: int32) {
    owns occupied[0..capacity];
    forall (k: int32) where 0 <= k and k < capacity {
        if occupied[k] == 0 {
            owns data[k..k + 1];
        }
    }
}

verifying "iterated_ownership_fold_fresh_heap_map.c";

void with_fresh_map(int32* data, int32 capacity) {
    requires 1 <= capacity;
    requires capacity <= 536870911;
    owns data[0..capacity];
} by {
    step();
    step();
    step();
    branch {
        true => {
            step_until(function.exit);
            close();
        }
        false => {}
    }
    step();
    loop {
        decreases to_integer(capacity) - to_integer(i);
        invariant 0 <= i and i <= capacity;
        invariant forall (k: int32) {
            0 <= k and k < i implies occupied[k] == 0
        };
        owns occupied[0..capacity];
        maintain by {
            mark iteration;
            step();
            step();
            have to_integer(at(iteration, i) + 1) == to_integer(at(iteration, i)) + 1;
            have 0 <= to_integer(capacity) - to_integer(at(iteration, i) + 1);
            have forall (k: int32) { 0 <= k and k < i implies occupied[k] == 0 } by {
                intro() {
                    intro() {
                        have 0 <= k;
                        have k < i;
                        if k < at(iteration, i) {
                            have at(iteration, occupied[k]) == 0 by {
                                have at(iteration, 0) <= at(iteration, k) and at(iteration, k) < at(iteration, i);
                                instantiate(forall (j: int32) {
                                    at(iteration, 0) <= at(iteration, j) and at(iteration, j) < at(iteration, i) implies
                                        at(iteration, occupied[j]) == at(iteration, 0)
                                }, k);
                                close();
                            }
                            have at(iteration, i) != k by { close() using { k < at(iteration, i); }; }
                            have at(iteration, separate(memory(occupied[i]), memory(occupied[k]))) by {
                                apply(separation::separate_elements(occupied, at(iteration, i), k));
                            }
                            have separate(loop(0).statement(0).footprint, memory(occupied[k])) by {
                                close() using { at(iteration, separate(memory(occupied[i]), memory(occupied[k]))); };
                            }
                            have at(loop(0).statement(0).exit, occupied[k]) == at(iteration, occupied[k]) by {
                                preserve(memory(occupied[k]), loop(0).statement(0));
                            }
                            have separate(loop(0).statement(1).footprint, memory(occupied[k])) by { close() using {}; }
                            have occupied[k] == at(loop(0).statement(1).entry, occupied[k]) by {
                                preserve(memory(occupied[k]), loop(0).statement(1));
                            }
                            close();
                        } else {
                            have k == at(iteration, i) by { close(); }
                            rewrite(k, at(iteration, i));
                            close();
                        }
                    }
                }
            }
            close();
        }
    }
    have i == capacity;
    have forall (k: int32) {
        0 <= k and k < capacity implies occupied[k] == 0
    } by {
        rewrite(capacity, i);
        close();
    }
    fold(arena_cells(data, occupied, capacity)[..]);
    unfold(arena_cells(data, occupied, capacity)[..]);
    step_until(function.exit);
    close();
}
```

```expect
pass
```
