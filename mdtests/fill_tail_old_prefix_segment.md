# fill_tail proves an old-value prefix

This checks that a memory-changing loop can prove an old-memory postcondition
when that unchanged-memory fact is stated as an explicit quantified invariant.
The prefix is outside the mutated suffix.

```c filename=fill_tail_old_prefix_segment.c
int32 fill_tail_old_prefix_segment(int32 p[], int32 n) {
    int32 i;
    i = 1;
    while (i < n) {
        p[i] = i;
        i = i + 1;
    }
    return n;
}
```

```click
verifying "fill_tail_old_prefix_segment.c";

int32 fill_tail_old_prefix_segment(int32 p[], int32 n) {
    requires n >= 1 and n <= 2147483647;
    consumes p[0..n];
    ensures prefix_unchanged: forall (k: int32) {
        0 <= k and k < 1 implies p[k] == old(p[k])
    };
} by {
    step();
    step();
    loop {
        decreases n - i;
        invariant i >= 1 and i <= n;
        invariant forall (k: int32) {
            0 <= k and k < 1 implies p[k] == old(p[k])
        };
        maintain by {
            mark iter;
            step();
            have forall (k: int32) {
                0 <= k and k < 1 implies p[k] == old(p[k])
            } by {
                intro() {
                    intro() {
                        instantiate(at(iter, forall (j: int32) { 0 <= j and j < 1 implies p[j] == old(p[j]) }), k);
                        have at(iter, p[k]) == old(p[k]) by { close(); }
                        have k < i by { close() using { k < 1; 1 <= i; }; }
                        have i != k by { close() using { k < i; }; }
                        have separate(memory(p[i]), memory(p[k])) by {
                            apply(click::separation::separate_elements(p, i, k));
                        }
                        have separate(loop(0).statement(0).footprint, memory(p[k])) by {
                            close() using { separate(memory(p[i]), memory(p[k])); };
                        }
                        have p[k] == at(iter, p[k]) by {
                            preserve(memory(p[k]), loop(0).statement(0));
                        }
                        close() using { p[k] == at(iter, p[k]); at(iter, p[k]) == old(p[k]); };
                    }
                }
            }
            step();
        }
    }
    step();
    close();
}
```

```expect
pass
```
