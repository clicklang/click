# A loop-body proof `match` rejoins through its interface

Each arm opens the cell and refolds it with its own constructor, so the arms
end the same way but hold cells with different models. `ensuring` names the
cell the rejoined body holds. The arms rejoin inside the body, as the arms of
a `branch` do, and the rest of the iteration (the C step and the invariants)
is checked once, on the one path that leaves the `match`, not once per arm.

```c filename=loop_body_proof_match_ensuring_rejoins.c
struct cell { int32 value; };

void spin(struct cell *node, int32 n) {
    int32 i;
    i = 0;
    while (i < n) {
        i = i + 1;
    }
}
```

```click
verifying "loop_body_proof_match_ensuring_rejoins.c";

spec enum Sign { Neg(int32), Pos(int32) }

resource cell(p: struct cell*) {
    field model: Sign;
    match model {
        Sign::Neg(value) => {
            owns p->value;
            fact p->value == value;
            fact value < 0;
        },
        Sign::Pos(value) => {
            owns p->value;
            fact p->value == value;
            fact value >= 0;
        },
    }
}

void spin(struct cell* node, int32 n) {
    requires n >= 0;
    requires node != 0;
    owns c: cell(node);
} by {
    step();
    step();
    loop {
        decreases n - i;
        owns c: cell(node);
        invariant i >= 0;
        invariant i <= n;

        initialize by solve();
        preserve by {
            match c.model ensuring {
                owns c: cell(node);
            } {
                Sign::Neg(value) => {
                    unfold(c);
                    let c = fold(cell(node), { model: Sign::Neg(value) });
                }
                Sign::Pos(value) => {
                    unfold(c);
                    let c = fold(cell(node), { model: Sign::Pos(value) });
                }
            }
            step();
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
                            have -2147483648 <= (to_integer(at(region(3).entry, i)) + 1) by {
                                arithmetic_certificate {
                                    premise 0: at(region(3).entry, i) >= at(region(3).entry, 0) =>
                                        at(region(3).entry, i) >= at(region(3).entry, 0);
                                    trivial => -2147483649 <= 0;
                                    add 0, 1 => (at(region(3).entry, 0) + -2147483649) <= (at(region(3).entry,
                                        to_integer(i)) + 0);
                                    conclusion 2;
                                }
                            }
                            have (to_integer(at(region(3).entry, i)) + 1) <= 2147483647 by {
                                arithmetic_certificate {
                                    negated_goal => 2147483647 < (to_integer(at(region(3).entry, i)) + 1);
                                    premise 0: at(region(3).entry, i) < at(region(3).entry, n) =>
                                        at(region(3).entry, i) < at(region(3).entry, n);
                                    type_range => to_integer(n) <= 2147483647;
                                    add 0, 1 => (2147483647 + 1 + (at(region(3).entry, to_integer(i)) + 1)) <=
                                        (to_integer(at(region(3).entry, i)) + 1 + at(region(3).entry,
                                        to_integer(n)));
                                    add 3, 2 => (2147483647 + 1 + (at(region(3).entry, to_integer(i)) + 1) +
                                        to_integer(n)) <= (to_integer(at(region(3).entry, i)) + 1 +
                                        at(region(3).entry, to_integer(n)) + 2147483647);
                                    conclusion 4;
                                }
                            }
                            have to_integer(i) == (to_integer(at(region(3).entry, i)) + 1) by {
                                arithmetic_certificate rules {
                                    premise 0: -2147483648 <= (to_integer(at(region(3).entry, i)) + 1) =>
                                        -2147483648 <= (to_integer(at(region(3).entry, i)) + 1);
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
                                less_equal_from_equal 1 => to_integer(i) <= (to_integer(at(region(3).entry, i))
                                    + 1);
                                add 0, 2 => (at(region(3).entry, to_integer(i)) + to_integer(i)) <
                                    (at(region(3).entry, to_integer(n)) + (to_integer(at(region(3).entry, i)) +
                                    1));
                                conclusion 3;
                            }
                        } and {
                            have -2147483648 <= (to_integer(at(region(3).entry, i)) + 1) by {
                                arithmetic_certificate {
                                    premise 0: at(region(3).entry, i) >= at(region(3).entry, 0) =>
                                        at(region(3).entry, i) >= at(region(3).entry, 0);
                                    trivial => -2147483649 <= 0;
                                    add 0, 1 => (at(region(3).entry, 0) + -2147483649) <= (at(region(3).entry,
                                        to_integer(i)) + 0);
                                    conclusion 2;
                                }
                            }
                            have (to_integer(at(region(3).entry, i)) + 1) <= 2147483647 by {
                                arithmetic_certificate {
                                    negated_goal => 2147483647 < (to_integer(at(region(3).entry, i)) + 1);
                                    premise 0: at(region(3).entry, i) < at(region(3).entry, n) =>
                                        at(region(3).entry, i) < at(region(3).entry, n);
                                    type_range => to_integer(n) <= 2147483647;
                                    add 0, 1 => (2147483647 + 1 + (at(region(3).entry, to_integer(i)) + 1)) <=
                                        (to_integer(at(region(3).entry, i)) + 1 + at(region(3).entry,
                                        to_integer(n)));
                                    add 3, 2 => (2147483647 + 1 + (at(region(3).entry, to_integer(i)) + 1) +
                                        to_integer(n)) <= (to_integer(at(region(3).entry, i)) + 1 +
                                        at(region(3).entry, to_integer(n)) + 2147483647);
                                    conclusion 4;
                                }
                            }
                            have to_integer(i) == (to_integer(at(region(3).entry, i)) + 1) by {
                                arithmetic_certificate rules {
                                    premise 0: -2147483648 <= (to_integer(at(region(3).entry, i)) + 1) =>
                                        -2147483648 <= (to_integer(at(region(3).entry, i)) + 1);
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
                                less_equal_from_equal 0 reverse => (to_integer(at(region(3).entry, i)) + 1) <=
                                    to_integer(i);
                                conclusion 1;
                            }
                        }
                    }
                }
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
