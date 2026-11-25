# fill3 verifies an array-parameter pointer loop

This checks C-style array parameter syntax, pointer-loop stores, loop
invariants, and post-state memory claims in one small example.

```c filename=fill3_array_loop.c
int32 fill3_array_loop(int32 p[3]) {
    int32 i;
    i = 0;
    while (i < 3) {
        p[i] = i;
        i = i + 1;
    }
    return p[2];
}
```

```click
verifying "fill3_array_loop.c";

int32 fill3_array_loop(int32 p[3]) {
    consumes p[0..3];
    ensures writes_first: p[0] == 0;
    ensures writes_second: p[1] == 1;
    ensures writes_third: p[2] == 2;
    ensures returns_third: result == 2;
} by {
    step();
    step();
    loop {
        decreases 3 - i;
        invariant i >= 0 and i <= 3;
        invariant forall (k: int32) {
            0 <= k and k < i implies p[k] == k
        };

        initialize by close();
        maintain by {
            mark before_store;
            step();
            step();
            have to_integer(i) == to_integer(at(before_store, i) + 1);
            have forall (k: int32) {
                0 <= k and k < i implies p[k] == k
            } by {
                intro() {
                    intro() {
                        if k < at(before_store, i) {
                            have at(before_store, 0 <= k and k < i) by { close(); }
                            instantiate(at(before_store, forall (j: int32) {
                                0 <= j and j < i implies p[j] == j
                            }), k);
                            have k != at(before_store, i) by { close(); }
                            have at(before_store, separate(memory(p[i]), memory(p[k]))) by {
                                apply(click::separation::separate_elements(p, at(before_store, i), k));
                            }
                            have separate(loop(0).statement(0).footprint, memory(p[k])) by {
                                close() using { at(before_store, separate(memory(p[i]), memory(p[k]))); };
                            }
                            have at(loop(0).statement(0).exit, p[k]) == at(before_store, p[k]) by {
                                preserve(memory(p[k]), loop(0).statement(0));
                            }
                            have separate(loop(0).statement(1).footprint, memory(p[k])) by { close(); }
                            have p[k] == at(loop(0).statement(1).entry, p[k]) by {
                                preserve(memory(p[k]), loop(0).statement(1));
                            }
                            close();
                        } else {
                            have k == at(before_store, i) by { close(); }
                            rewrite(k, at(before_store, i));
                            close();
                        }
                    }
                }
            }
        }
    }
    step();
    have 3 <= at(loop(0).exit, i) by close();
    have 0 < at(loop(0).exit, i) by {
        apply(click::integer::int32_less_than_less_equal_transitive(0, 3, at(loop(0).exit, i)));
    }
    have 1 < at(loop(0).exit, i) by {
        apply(click::integer::int32_less_than_less_equal_transitive(1, 3, at(loop(0).exit, i)));
    }
    have 2 < at(loop(0).exit, i) by {
        apply(click::integer::int32_less_than_less_equal_transitive(2, 3, at(loop(0).exit, i)));
    }
    close();
}
```

```expect
pass
```
