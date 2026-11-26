# A guarded quantified postcondition after a loop expands and re-verifies

`fill` sets every cell of `occ` to `1` and returns `1`, the shape of an
allocator's occupancy postcondition: `result == 1 implies forall (k: int32)
{ ... }`. After the loop, `close()` closes the claim by introducing the guard
and the binder and instantiating the loop invariant; claim expansion renders
that proof as a `have` of the claim followed by `close()`. The `have`
and the claim lower the guarded quantifier with independent fresh binders,
and the rewrite used to fail with "`known` did not match any current
proposition goal". The expansion regression in
`src/surface/tests/expansion_tests.rs` expands this claim and re-verifies the
rewrite.

```c filename=guarded_quantified_postcondition_after_loop.c
int fill(int32* occ, int32 cap) {
    int32 i = 0;
    while (i < cap) {
        occ[i] = 1;
        i = i + 1;
    }
    return 1;
}
```

```click
import click::separation;

verifying "guarded_quantified_postcondition_after_loop.c";

int fill(int32* occ, int32 cap) {
    owns occ[0..cap];
    requires 0 <= cap;
    ensures result == 1 implies forall (k: int32) {
        0 <= k and k < cap implies occ[k] == 1
    };
} by {
    step();
    step();
    loop {
        decreases to_integer(cap) - to_integer(i);
        invariant 0 <= i;
        invariant i <= cap;
        invariant forall (k: int32) { 0 <= k and k < i implies occ[k] == 1 };
        owns occ[0..cap];
        maintain by {
            mark iteration;
            step();
            step();
            have to_integer(at(iteration, i) + 1) == to_integer(at(iteration, i)) + 1;
            have 0 <= to_integer(cap) - to_integer(at(iteration, i) + 1);
            have forall (k: int32) { 0 <= k and k < i implies occ[k] == 1 } by {
                intro() {
                    intro() {
                        have 0 <= k;
                        have k < i;
                        if k < at(iteration, i) {
                            have at(iteration, occ[k]) == 1 by {
                                have at(iteration, 0) <= at(iteration, k) and at(iteration, k) < at(iteration, i);
                                instantiate(forall (cell: int32) {
                                    at(iteration, 0) <= at(iteration, cell) and at(iteration, cell) < at(iteration, i) implies
                                        at(iteration, occ[cell]) == at(iteration, 1)
                                }, k);
                                close();
                            }
                            have at(iteration, i) != k by { close() using { k < at(iteration, i); }; }
                            have at(iteration, separate(memory(occ[i]), memory(occ[k]))) by {
                                apply(separation::separate_elements(occ, at(iteration, i), k));
                            }
                            have separate(loop(0).statement(0).footprint, memory(occ[k])) by {
                                close() using { at(iteration, separate(memory(occ[i]), memory(occ[k]))); };
                            }
                            have at(loop(0).statement(0).exit, occ[k]) == at(iteration, occ[k]) by {
                                preserve(memory(occ[k]), loop(0).statement(0));
                            }
                            have separate(loop(0).statement(1).footprint, memory(occ[k])) by { close() using {}; }
                            have occ[k] == at(loop(0).statement(1).entry, occ[k]) by {
                                preserve(memory(occ[k]), loop(0).statement(1));
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
}
```

```expect
pass
```
