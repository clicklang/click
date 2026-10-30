# A proof `match` runs at a loop-body frontier

At an arbitrary loop head a binder's model is a fresh symbolic value, so
`unfold(c)` has no constructor to open. A proof `match` on `c.model` inside
`preserve` supplies one: each arm's path gets the constructor equation with
fresh bindings, and the arm that the invariants exclude closes by
`contradiction` without running an iteration.

Each arm runs to the loop's own boundary rather than to function exit. Nothing
joins the arms: the live arm refolds its own instance and closes the invariants
on its own path, so the back edge sees the resource state that arm produced.

```c filename=loop_body_proof_match.c
struct cell { int32 value; };

int32 spin(struct cell *node, int32 n) {
    int32 i;
    i = 0;
    while (i < n) {
        i = i + 1;
    }
    return node->value;
}
```

```click
verifying "loop_body_proof_match.c";

spec enum Maybe { None, Some(int32) }

resource cell(p: struct cell*) {
    field model: Maybe;
    match model {
        Maybe::None => { fact p == 0; },
        Maybe::Some(value) => { owns p->value; fact p->value == value; },
    }
}

int32 spin(struct cell* node, int32 n) {
    requires n >= 0;
    requires node != 0;
    owns c: cell(node);
    requires c.model != Maybe::None;
    ensures c.model == old(c.model);
} by {
    step();
    step();
    loop {
        decreases n - i;
        owns c: cell(node);
        invariant i >= 0;
        invariant i <= n;
        invariant c.model == old(c.model);
        invariant c.model != Maybe::None;

        initialize by solve();
        preserve by {
            match c.model {
                Maybe::None => { contradiction(c.model == Maybe::None); },
                Maybe::Some(value) => {
                    have Maybe::Some(value) == old(c.model) by {
                        solve() using { c.model == Maybe::Some(value); c.model == old(c.model); };
                    }
                    unfold(c);
                    step();
                    let c = fold(cell(node), { model: Maybe::Some(value) });
                    close_invariants() by {
                        both {
                            arithmetic_certificate signed_int32 {
                                premise 0: at(region(3).entry, i) >= at(region(3).entry, 0) => at(region(3).entry, i) >=
                                    at(region(3).entry, 0);
                                premise 1: at(region(3).entry, i) < at(region(3).entry, n) => at(region(3).entry, i) <
                                    at(region(3).entry, n);
                                int32_range => n <= 2147483647;
                                add 1, 2 => (at(region(3).entry, i) + n) < (at(region(3).entry, n) +
                                    2147483647);
                                interval_from_affine 0 (at(region(3).entry, i)) (0) (2147483647);
                                interval_from_affine 3 (at(region(3).entry, i)) (-2147483648) (2147483646);
                                interval_intersect 4, 5 (0) (2147483646);
                                interval_atom (1) (1) (1);
                                interval_add_bounded 6, 7 (1) (2147483647);
                                trivial => -1 <= 0;
                                add 0, 9 => (at(region(3).entry, 0) + -1) <= (at(region(3).entry, i) + 0);
                                affine_conclusion 10 8 => (i as int32) >= (0 as int32);
                                conclusion 11;
                            }
                        } and {
                            both {
                                intro();
                                arithmetic_certificate signed_int32 {
                                    premise 0: at(region(3).entry, i) < at(region(3).entry, n) => at(region(3).entry, i)
                                        < at(region(3).entry, n);
                                    int32_range => n <= 2147483647;
                                    add 0, 1 => (at(region(3).entry, i) + n) < (at(region(3).entry, n) +
                                        2147483647);
                                    interval_from_affine 2 (at(region(3).entry, i)) (-2147483648) (2147483646);
                                    interval_atom (1) (1) (1);
                                    interval_add_bounded 3, 4 (-2147483647) (2147483647);
                                    affine_conclusion 0 5 => (i as int32) <= (n as int32);
                                    conclusion 6;
                                }
                            } and {
                                both {
                                    intro();
                                    intro();
                                    assumption();
                                } and {
                                    both {
                                        intro();
                                        intro();
                                        intro();
                                        normalize();
                                    } and {
                                        both {
                                            have -2147483648 <= (to_integer(at(region(3).entry, i)) + 1) by {
                                                arithmetic_certificate {
                                                    premise 0: at(region(3).entry, i) >= at(region(3).entry, 0) =>
                                                        at(region(3).entry, i) >= at(region(3).entry, 0);
                                                    trivial => -2147483649 <= 0;
                                                    add 0, 1 => (at(region(3).entry, 0) + -2147483649) <=
                                                        (at(region(3).entry, to_integer(i)) + 0);
                                                    conclusion 2;
                                                }
                                            }
                                            have (to_integer(at(region(3).entry, i)) + 1) <= 2147483647 by {
                                                arithmetic_certificate {
                                                    negated_goal => 2147483647 < (to_integer(at(region(3).entry, i)) +
                                                        1);
                                                    premise 0: at(region(3).entry, i) < at(region(3).entry, n) =>
                                                        at(region(3).entry, i) < at(region(3).entry, n);
                                                    type_range => to_integer(n) <= 2147483647;
                                                    add 0, 1 => (2147483647 + 1 + (at(region(3).entry, to_integer(i)) +
                                                        1)) <= (to_integer(at(region(3).entry, i)) + 1 +
                                                        at(region(3).entry, to_integer(n)));
                                                    add 3, 2 => (2147483647 + 1 + (at(region(3).entry, to_integer(i)) +
                                                        1) + to_integer(n)) <= (to_integer(at(region(3).entry, i)) + 1 +
                                                        at(region(3).entry, to_integer(n)) + 2147483647);
                                                    conclusion 4;
                                                }
                                            }
                                            have to_integer(i) == (to_integer(at(region(3).entry, i)) + 1) by {
                                                arithmetic_certificate rules {
                                                    premise 0: -2147483648 <= (to_integer(at(region(3).entry, i)) + 1)
                                                        => -2147483648 <= (to_integer(at(region(3).entry, i)) + 1);
                                                    premise 1: (to_integer(at(region(3).entry, i)) + 1) <= 2147483647 =>
                                                        (to_integer(at(region(3).entry, i)) + 1) <= 2147483647;
                                                    integer_operation_identity bounds [0, 1] => to_integer(i) ==
                                                        (to_integer(at(region(3).entry, i)) + 1);
                                                    conclusion 0;
                                                }
                                            }
                                            arithmetic_certificate {
                                                premise 0: at(region(3).entry, i) < at(region(3).entry, n) =>
                                                    at(region(3).entry, i) < at(region(3).entry, n);
                                                premise 1: to_integer(i) == (to_integer(at(region(3).entry, i)) + 1) =>
                                                    to_integer(i) == (to_integer(at(region(3).entry, i)) + 1);
                                                less_equal_from_equal 1 => to_integer(i) <=
                                                    (to_integer(at(region(3).entry, i)) + 1);
                                                add 0, 2 => (at(region(3).entry, to_integer(i)) + to_integer(i)) <
                                                    (at(region(3).entry, to_integer(n)) +
                                                    (to_integer(at(region(3).entry, i)) + 1));
                                                conclusion 3;
                                            }
                                        } and {
                                            have -2147483648 <= (to_integer(at(region(3).entry, i)) + 1) by {
                                                arithmetic_certificate {
                                                    premise 0: at(region(3).entry, i) >= at(region(3).entry, 0) =>
                                                        at(region(3).entry, i) >= at(region(3).entry, 0);
                                                    trivial => -2147483649 <= 0;
                                                    add 0, 1 => (at(region(3).entry, 0) + -2147483649) <=
                                                        (at(region(3).entry, to_integer(i)) + 0);
                                                    conclusion 2;
                                                }
                                            }
                                            have (to_integer(at(region(3).entry, i)) + 1) <= 2147483647 by {
                                                arithmetic_certificate {
                                                    negated_goal => 2147483647 < (to_integer(at(region(3).entry, i)) +
                                                        1);
                                                    premise 0: at(region(3).entry, i) < at(region(3).entry, n) =>
                                                        at(region(3).entry, i) < at(region(3).entry, n);
                                                    type_range => to_integer(n) <= 2147483647;
                                                    add 0, 1 => (2147483647 + 1 + (at(region(3).entry, to_integer(i)) +
                                                        1)) <= (to_integer(at(region(3).entry, i)) + 1 +
                                                        at(region(3).entry, to_integer(n)));
                                                    add 3, 2 => (2147483647 + 1 + (at(region(3).entry, to_integer(i)) +
                                                        1) + to_integer(n)) <= (to_integer(at(region(3).entry, i)) + 1 +
                                                        at(region(3).entry, to_integer(n)) + 2147483647);
                                                    conclusion 4;
                                                }
                                            }
                                            have to_integer(i) == (to_integer(at(region(3).entry, i)) + 1) by {
                                                arithmetic_certificate rules {
                                                    premise 0: -2147483648 <= (to_integer(at(region(3).entry, i)) + 1)
                                                        => -2147483648 <= (to_integer(at(region(3).entry, i)) + 1);
                                                    premise 1: (to_integer(at(region(3).entry, i)) + 1) <= 2147483647 =>
                                                        (to_integer(at(region(3).entry, i)) + 1) <= 2147483647;
                                                    integer_operation_identity bounds [0, 1] => to_integer(i) ==
                                                        (to_integer(at(region(3).entry, i)) + 1);
                                                    conclusion 0;
                                                }
                                            }
                                            arithmetic_certificate {
                                                premise 0: to_integer(i) == (to_integer(at(region(3).entry, i)) + 1) =>
                                                    to_integer(i) == (to_integer(at(region(3).entry, i)) + 1);
                                                less_equal_from_equal 0 reverse => (to_integer(at(region(3).entry, i)) +
                                                    1) <= to_integer(i);
                                                conclusion 1;
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                },
            }
        }
    }
    step();
    solve();
}
```

```expect
pass
```
