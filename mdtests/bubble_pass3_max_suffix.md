# bubble_pass3 moves the maximum to the end

This checks the first loop-invariant sorting step: one bubble-sort pass over
three cells should establish that every earlier cell is less than or equal to
the final cell. It intentionally does not prove permutation.

The invariant depends on whether the swap ran, so the two arms of the C `if`
cannot be joined keeping only what they agree on, which is all the automatic
loop closer does at an `if`. The body is written out, and its `branch` says
what both arms establish: after the `if`, `p[j] <= p[j + 1]`, and every
earlier cell is at most `p[j + 1]`. Each arm proves both from what it did,
and the rest of the iteration is checked once on the path that leaves the
`if`.

The interface includes `defined(j + 1)`, proved in both arms. Its facts
can use `p[j + 1]` only while carrying the condition that `j + 1` does not
overflow
([`an_interface_fact_needs_its_terms_defined_in_each_arm.md`](an_interface_fact_needs_its_terms_defined_in_each_arm.md)).

The swap arm explicitly preserves earlier cells across each store using
element separation and transport certificates.

```c filename=bubble_pass3.c
int32 bubble_pass3(int32 p[3]) {
    int32 j;
    int32 tmp;
    j = 0;
    while (j < 2) {
        if (p[j + 1] < p[j]) {
            tmp = p[j];
            p[j] = p[j + 1];
            p[j + 1] = tmp;
        }
        j = j + 1;
    }
    return 0;
}
```

```click
import click::separation;
verifying "bubble_pass3.c";

predicate all_le_range(p: int32[], lo: int32, hi: int32, x: int32) {
    forall (k: int32) {
        0 <= k and lo <= k and k < hi implies p[k] <= x
    }
}

int32 bubble_pass3(int32 p[3]) {
    consumes p[0..3];
    ensures max_at_end: all_le_range(p, 0, 2, p[2]);
} by {
    step();
    step();
    step();
    loop {
        decreases 2 - j;
        invariant j >= 0 and j <= 2;
        invariant all_le_range(p, 0, j, p[j]);
        initialize by {
            unfold(all_le_range);
            solve();
        }
        preserve by {
            branch ensuring {
                fact defined(j + 1);
                fact p[j] <= p[j + 1];
                fact all_le_range(p, 0, j, p[j + 1]);
            } then {
                step();
                step();
                step();
                have defined(j + 1);
                have p[j] <= p[j + 1];
                have all_le_range(p, 0, j, p[j + 1]) by {
                    if j == 0 {
                        unfold(all_le_range);
                        solve();
                    } else {
                        have j == 1 by solve();
                        have separate(memory(p[1]), memory(p[0])) by {
                            apply(separation::elements(p, 1 as uint64, 0 as uint64)) using {};
                        }
                        have separate(memory(p[2]), memory(p[0])) by {
                            apply(separation::elements(p, 2 as uint64, 0 as uint64)) using {};
                        }
                        have separate(memory(p[j]), memory(p[0])) by { rewrite(j == 1); assumption(); }
                        have separate(memory(p[j + 1]), memory(p[0])) by { rewrite(j == 1); assumption(); }
                        have separate(loop(0).statement(0).statement(1).footprint, memory(p[0])) by {
                            normalize() using { separate(memory(p[j]), memory(p[0])); };
                        }
                        have at(loop(0).statement(0).statement(1).exit, p[0]) == at(loop(0).statement(0).statement(1).entry, p[0]) by {
                            transport_certificate {
                                premise 0: separate(loop(0).statement(0).statement(1).footprint, memory(p[0]))
                                    => separate(loop(0).statement(0).statement(1).footprint, memory(p[0]));
                                preserve 0 => at(loop(0).statement(0).statement(1).exit, p[0]) == at(loop(0).statement(0).statement(1).entry, p[0]);
                                conclusion 1;
                            }
                        }
                        have separate(loop(0).statement(0).statement(2).footprint, memory(p[0])) by {
                            normalize() using { separate(memory(p[j + 1]), memory(p[0])); };
                        }
                        have at(loop(0).statement(0).statement(2).exit, p[0]) == at(loop(0).statement(0).statement(2).entry, p[0]) by {
                            transport_certificate {
                                premise 0: separate(loop(0).statement(0).statement(2).footprint, memory(p[0]))
                                    => separate(loop(0).statement(0).statement(2).footprint, memory(p[0]));
                                preserve 0 => at(loop(0).statement(0).statement(2).exit, p[0]) == at(loop(0).statement(0).statement(2).entry, p[0]);
                                conclusion 1;
                            }
                        }
                        unfold(all_le_range);
                        intro(); intro();
                        have k == 0 by solve();
                        solve();
                    }
                }
            } else {
                have defined(j + 1);
                have p[j] <= p[j + 1];
                have all_le_range(p, 0, j, p[j + 1]) by {
                    unfold(all_le_range);
                    solve();
                }
            }
            step();
            unfold(all_le_range);
            close_invariants();
        }
        owns p[0..3];
    }
    step();
    unfold(all_le_range);
    solve();
}
```

```expect
pass
```
