# bubble_sort3_two_pass proves sortedness with loop invariants

This checks that a fixed-size two-pass bubble sort over three cells can prove
sortedness from loop VCs and quantified invariants, without bounded execution.

The proof below is a saved expansion of explicit branch arguments and invariant
closure bodies. Each swap preserves untouched cells with explicit separation
and one-store `preserve` steps. The two stored-value equalities name the
respective store exits, and ordinary arithmetic combines the resulting facts.
No written or expanded `transport` is needed; the C and invariants are unchanged.

```c filename=bubble_sort3_two_pass.c
int32 bubble_sort3_two_pass(int32 p[3]) {
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
    j = 0;
    while (j < 1) {
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
verifying "bubble_sort3_two_pass.c";

predicate sorted(p: int32[], n: int32) {
    sorted_range(p, 0, n)
}

predicate sorted_range(p: int32[], lo: int32, hi: int32) {
    forall (i: int32) {
        forall (j: int32) {
            0 <= i and 0 <= j and lo <= i and i < j and j < hi implies p[i] <= p[j]
        }
    }
}

predicate all_le_range(p: int32[], lo: int32, hi: int32, x: int32) {
    forall (k: int32) {
        0 <= k and lo <= k and k < hi implies p[k] <= x
    }
}

int32 bubble_sort3_two_pass(int32 p[3]) {
    requires viewable(p[0..3]);
    consumes p[0..3];
    ensures sorted: sorted(p, 3);
} by {
    step();
    step();
    step();
    loop {
        decreases (2 - j);
        invariant j >= 0 and j <= 2;
        invariant all_le_range(p, 0, j, p[j]);
        initialize by {
            have j >= 0 and j <= 2 by {
                unfold(all_le_range(p, 0, j, p[j]));
                all positional {
                    left => {
                        normalize();
                    }
                    right => {
                        normalize();
                    }
                }
            }
            have all_le_range(p, 0, j, p[j]) by {
                unfold(all_le_range(p, 0, j, p[j]));
                enumerate();
            }
        }
        preserve by {
            if p[(j + 1)] < p[j] {
                unfold(all_le_range(p, 0, j, p[j]));
                step();
                step();
                step();
                step();
                step();
                have all_le_range(p, 0, j, p[j]) by {
                    unfold(all_le_range(p, 0, j, p[j]));
                    intro();
                    intro();
                    if k < (j - 1) {
                        have k < at(region(4).entry, j);
                        instantiate(forall (__click_q0: int32) { at(region(6).entry, 0) <= at(region(6).entry, __click_q0) and at(region(6).entry, 0) <= at(region(6).entry, __click_q0) and at(region(6).entry, __click_q0) < at(region(6).entry, j) implies at(region(6).entry, p[__click_q0]) <= at(region(6).entry, tmp) }, k);
                        have at(region(4).entry, j) != k by { solve(); }
                        have at(region(4).entry, separate(memory(p[j]), memory(p[k]))) by {
                            apply(click::separation::separate_elements(p, at(region(4).entry, j), k)) using { at(region(4).entry, j) != k; };
                        }
                        have separate(statement(3).statement(0).statement(1).footprint, memory(p[k])) by {
                            normalize() using { at(region(4).entry, separate(memory(p[j]), memory(p[k]))); };
                        }
                        have at(statement(3).statement(0).statement(1).exit, p[k]) == at(statement(3).statement(0).statement(1).entry, p[k]) by {
                            preserve(memory(p[k]), statement(3).statement(0).statement(1));
                        }
                        have j != k by { solve(); }
                        have separate(memory(p[j]), memory(p[k])) by {
                            apply(click::separation::separate_elements(p, j, k)) using { j != k; };
                        }
                        have separate(statement(3).statement(0).statement(2).footprint, memory(p[k])) by {
                            normalize() using { separate(memory(p[j]), memory(p[k])); };
                        }
                        have at(statement(3).statement(0).statement(2).exit, p[k]) == at(statement(3).statement(0).statement(2).entry, p[k]) by {
                            preserve(memory(p[k]), statement(3).statement(0).statement(2));
                        }
                        known();
                    } else {
                        have k == (j - 1);
                        have to_integer(k) == to_integer(at(region(4).entry, j));
                        have j != k by { solve(); }
                        have separate(memory(p[j]), memory(p[k])) by {
                            apply(click::separation::separate_elements(p, j, k)) using { j != k; };
                        }
                        have separate(statement(3).statement(0).statement(2).footprint, memory(p[k])) by {
                            normalize() using { separate(memory(p[j]), memory(p[k])); };
                        }
                        have at(statement(3).statement(0).statement(2).exit, p[k]) == at(statement(3).statement(0).statement(2).entry, p[k]) by {
                            preserve(memory(p[k]), statement(3).statement(0).statement(2));
                        }

                        have p[k] == at(region(7).entry, p[(j + 1)]) by { rewrite(k, at(region(4).entry, j)); known(); }
                        have p[j] == at(region(7).entry, tmp) by { known(); }
                        solve() using {
                            k == at(region(4).entry, j);
                            p[k] == at(region(7).entry, p[(j + 1)]);
                            p[j] == at(region(7).entry, tmp);
                            at(region(7).entry, p[(j + 1)]) < at(region(7).entry, tmp);
                        };
                    }
                }
            } else {
                unfold(all_le_range(p, 0, j, p[j]));
                step();
                step();
                step();
                have all_le_range(p, 0, j, p[j]) by {
                    unfold(all_le_range(p, 0, j, p[j]));
                    intro();
                    intro();
                    if k < (j - 1) {
                        have k < at(region(4).entry, j);
                        instantiate(forall (__click_q0: int32) { at(region(9).entry, 0) <= at(region(9).entry, __click_q0) and at(region(9).entry, 0) <= at(region(9).entry, __click_q0) and at(region(9).entry, __click_q0) < at(region(9).entry, j) implies at(region(9).entry, p[__click_q0]) <= at(region(9).entry, p[j]) }, k);
                        have p[k] <= p[j] by {
                            solve() using {
                                at(region(9).entry, p[k]) <= at(region(9).entry, p[j]);
                                not at(region(9).entry, p[(j + 1)]) < at(region(9).entry, p[j]);
                            };
                        }
                        known();
                    } else {
                        have k == (j - 1);
                        have to_integer(k) == to_integer(at(region(4).entry, j));
                        rewrite(k, at(region(4).entry, j));
                        have at(region(9).entry, p[(j + 1)]) >= at(region(9).entry, p[j]);
                        solve() using {
                            at(region(9).entry, p[(j + 1)]) >= at(region(9).entry, p[j]);
                        };
                    }
                }
            }
        }
    }
    unfold(all_le_range(p, 0, j, p[j]));
    step();
    loop {
        decreases (1 - j);
        invariant j >= 0 and j <= 1;
        invariant all_le_range(p, 0, 2, p[2]);
        invariant all_le_range(p, 0, j, p[j]);
        initialize by {
            have j >= 0 and j <= 1 by {
                unfold(all_le_range(p, 0, j, p[j]));
                all positional {
                    left => {
                        normalize();
                    }
                    right => {
                        normalize();
                    }
                }
            }
            have all_le_range(p, 0, 2, p[2]) by {
                unfold(all_le_range(p, 0, 2, p[2]));
                intro();
                intro();
                have at(region(10).entry, 0) <= at(region(10).entry, k) and at(region(10).entry, 0) <= at(region(10).entry, k) and at(region(10).entry, k) < at(region(10).entry, j);
                instantiate(forall (__click_q0: int32) { at(region(10).entry, 0) <= at(region(10).entry, __click_q0) and at(region(10).entry, 0) <= at(region(10).entry, __click_q0) and at(region(10).entry, __click_q0) < at(region(10).entry, j) implies at(region(10).entry, p[__click_q0]) <= at(region(10).entry, p[j]) }, k);
                have at(loop(0).exit, j) == 2 by { solve(); }
                have at(region(10).entry, p[j]) == p[2] by {
                    normalize() using { at(loop(0).exit, j) == 2; };
                }
                solve() using {
                    at(region(10).entry, p[k]) <= at(region(10).entry, p[j]);
                    at(region(10).entry, p[j]) == p[2];
                };
            }
            have all_le_range(p, 0, j, p[j]) by {
                unfold(all_le_range(p, 0, j, p[j]));
                enumerate();
            }
        }
        preserve by {
            if p[(j + 1)] < p[j] {
                unfold(all_le_range(p, 0, j, p[j]));
                have j == 0 by {
                    have j <= 0;
                    solve() using {
                        j <= 0;
                        j >= 0;
                    };
                }
                unfold(all_le_range(p, 0, 2, p[2]));
                have p[0] <= p[2] by {
                    instantiate(forall (k: int32) { 0 <= k and 0 <= k and k < 2 implies p[k] <= p[2] }, 0);
                    known();
                }
                have p[1] <= p[2] by {
                    instantiate(forall (k: int32) { 0 <= k and 0 <= k and k < 2 implies p[k] <= p[2] }, 1);
                    known();
                }
                mark before_swap;
                unfold(all_le_range(p, 0, j, p[j]));
                step();
                step();
                step();
                step();
                step();
                have at(before_swap, j) != 2 by { solve(); }
                have at(before_swap, separate(memory(p[j]), memory(p[2]))) by {
                    apply(click::separation::separate_elements(p, at(before_swap, j), 2)) using { at(before_swap, j) != 2; };
                }
                have separate(statement(5).statement(0).statement(1).footprint, memory(p[2])) by {
                    normalize() using { at(before_swap, separate(memory(p[j]), memory(p[2]))); };
                }
                have at(statement(5).statement(0).statement(1).exit, p[2]) == at(statement(5).statement(0).statement(1).entry, p[2]) by {
                    preserve(memory(p[2]), statement(5).statement(0).statement(1));
                }
                have j != 2 by { solve(); }
                have separate(memory(p[j]), memory(p[2])) by {
                    apply(click::separation::separate_elements(p, j, 2)) using { j != 2; };
                }
                have separate(statement(5).statement(0).statement(2).footprint, memory(p[2])) by {
                    normalize() using { separate(memory(p[j]), memory(p[2])); };
                }
                have at(statement(5).statement(0).statement(2).exit, p[2]) == at(statement(5).statement(0).statement(2).entry, p[2]) by {
                    preserve(memory(p[2]), statement(5).statement(0).statement(2));
                }
                have j != 0 by { solve(); }
                have separate(memory(p[j]), memory(p[0])) by {
                    apply(click::separation::separate_elements(p, j, 0)) using { j != 0; };
                }
                have separate(statement(5).statement(0).statement(2).footprint, memory(p[0])) by {
                    normalize() using { separate(memory(p[j]), memory(p[0])); };
                }
                have at(statement(5).statement(0).statement(2).exit, p[0]) == at(statement(5).statement(0).statement(2).entry, p[0]) by {
                    preserve(memory(p[0]), statement(5).statement(0).statement(2));
                }
                have at(statement(5).statement(0).statement(1).exit, p[0]) == at(before_swap, p[1]) by {
                    normalize() using { at(before_swap, j) == 0; };
                }
                have p[0] == at(before_swap, p[1]) by { known(); }
                have at(statement(5).statement(0).statement(2).exit, p[1]) == at(before_swap, p[0]) by {
                    normalize() using { at(before_swap, j) == 0; };
                }
                have p[1] == at(before_swap, p[0]) by { known(); }
                have p[2] == at(before_swap, p[2]) by { known(); }
                have p[0] <= p[2] by { solve() using { p[0] == at(before_swap, p[1]); p[2] == at(before_swap, p[2]); at(before_swap, p[1] <= p[2]); }; }
                have p[1] <= p[2] by { solve() using { p[1] == at(before_swap, p[0]); p[2] == at(before_swap, p[2]); at(before_swap, p[0] <= p[2]); }; }
                have forall (k: int32) { 0 <= k and 0 <= k and k < 2 implies p[k] <= p[2] } by {
                    enumerate();
                }
                have j == 1 by {
                    rewrite(at(region(17).entry, j), at(region(17).entry, 0));
                    normalize();
                }
                have p[0] < p[1] by { known(); }
                have p[0] <= p[1] by {
                    solve() using {
                        p[0] < p[1];
                    };
                }
                have all_le_range(p, 0, j, p[j]) by {
                    unfold(all_le_range(p, 0, j, p[j]));
                    rewrite(j, 1);
                    enumerate();
                }
            } else {
                unfold(all_le_range(p, 0, j, p[j]));
                have j == 0 by {
                    have j <= 0;
                    solve() using {
                        j <= 0;
                        j >= 0;
                    };
                }
                unfold(all_le_range(p, 0, 2, p[2]));
                have p[0] <= p[2] by {
                    instantiate(forall (k: int32) { 0 <= k and 0 <= k and k < 2 implies p[k] <= p[2] }, 0);
                    known();
                }
                have p[1] <= p[2] by {
                    instantiate(forall (k: int32) { 0 <= k and 0 <= k and k < 2 implies p[k] <= p[2] }, 1);
                    known();
                }
                mark before_swap;
                unfold(all_le_range(p, 0, j, p[j]));
                step();
                step();
                step();
                have j == 1 by {
                    rewrite(at(region(17).entry, j), at(region(17).entry, 0));
                    normalize();
                }
                have not p[1] < p[0] by { known(); }
                have p[0] <= p[1] by {
                    have p[0] <= p[1] by {
                        solve() using {
                            not p[1] < p[0];
                        };
                    }
                    have p[0] <= p[1] by {
                        solve() using {
                            not at(region(18).entry, p[1]) < at(region(18).entry, p[0]);
                        };
                    }
                    solve() using {
                        at(region(18).entry, p[1]) >= at(region(18).entry, p[0]);
                    };
                }
                have all_le_range(p, 0, j, p[j]) by {
                    unfold(all_le_range(p, 0, j, p[j]));
                    rewrite(j, 1);
                    enumerate();
                }
            }
        }
    }
    unfold(all_le_range(p, 0, j, p[j]));
    unfold(all_le_range(p, 0, 2, p[2]));
    step();
    have sorted(p, 3) by {
        unfold(sorted(p, 3));
        unfold(sorted_range(p, 0, 3));
        have p[0] <= p[1] by {
            have 0 <= 0 and at(loop(1).exit, 0) <= 0 and 0 < at(loop(1).exit, j);
            instantiate(forall (k: int32) { 0 <= k and at(loop(1).exit, 0) <= k and k < at(loop(1).exit, j) implies at(loop(1).exit, p)[k] <= at(loop(1).exit, p[j]) }, 0);
            have at(loop(1).exit, j) == 1 by { solve(); }
            have at(loop(1).exit, p[j]) == p[1] by {
                normalize() using { at(loop(1).exit, j) == 1; };
            }
            solve() using {
                at(loop(1).exit, p)[0] <= at(loop(1).exit, p[j]);
                at(loop(1).exit, p[j]) == p[1];
            };
        }
        have p[1] <= p[2] by {
            instantiate(forall (k: int32) { 0 <= k and 0 <= k and k < 2 implies p[k] <= p[2] }, 1);
            known();
        }
        have p[0] <= p[2] by {
            instantiate(forall (k: int32) { 0 <= k and 0 <= k and k < 2 implies p[k] <= p[2] }, 0);
            known();
        }
        enumerate();
    }
    known();
}
```

```expect
pass
```
