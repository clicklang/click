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

        initialize by simp;
        preserve by {
            match c.model ensuring {
                owns c: cell(node);
            } {
                Sign::Neg(value) => {
                    unfold(c);
                    let c = fold(cell(node), { model: Sign::Neg(value) });
                },
                Sign::Pos(value) => {
                    unfold(c);
                    let c = fold(cell(node), { model: Sign::Pos(value) });
                },
            }
            step();
            close_invariants by {
                both {
                    apply(int32_increment_greater_equal_lower_bound(at(statement(3).entry, i), at(statement(3).entry, 0), at(statement(3).entry, n))) using {
                        at(statement(3).entry, i) >= at(statement(3).entry, 0);
                        at(statement(3).entry, i) < at(statement(3).entry, n);
                    }
                } and {
                    both {
                        intro();
                        apply(int32_increment_upper_bound(at(statement(3).entry, i), at(statement(3).entry, n))) using {
                            at(statement(3).entry, i) < at(statement(3).entry, n);
                        }
                    } and {
                            both {
                                arithmetic_certificate signed_int32 {
                                    premise 0: n >= 0 => n >= 0;
                                    premise 1: at(statement(3).entry, i) >= at(statement(3).entry, 0) => at(statement(3).entry, i) >= at(statement(3).entry, 0);
                                    premise 2: at(statement(3).entry, i) < at(statement(3).entry, n) => at(statement(3).entry, i) < at(statement(3).entry, n);
                                    interval_from_affine 0 (n) (0) (2147483647);
                                    interval_from_affine 1 (at(statement(3).entry, i)) (0) (2147483647);
                                    interval_subtract 3, 4 3 (-2147483647) (2147483647);
                                    interval_atom (1) (1) (1);
                                    interval_subtract 5, 6 5 (-2147483648) (2147483646);
                                    affine_conclusion 2 7 => 0 <= ((n - at(statement(3).entry, i)) - 1);
                                    conclusion 8;
                                }
                            } and {
                                arithmetic_certificate signed_int32 {
                                    premise 0: n >= 0 => n >= 0;
                                    premise 1: at(statement(3).entry, i) >= at(statement(3).entry, 0) => at(statement(3).entry, i) >= at(statement(3).entry, 0);
                                    interval_from_affine 0 (n) (0) (2147483647);
                                    interval_from_affine 1 (at(statement(3).entry, i)) (0) (2147483647);
                                    interval_subtract 2, 3 2 (-2147483647) (2147483647);
                                    interval_atom (1) (1) (1);
                                    interval_subtract 4, 5 4 (-2147483648) (2147483646);
                                    interval_subtract 2, 3 2 (-2147483647) (2147483647);
                                    trivial => 0 <= 0;
                                    affine_conclusion_pair 8 6 7 => ((n - at(statement(3).entry, i)) - 1) < (n - at(statement(3).entry, i));
                                    conclusion 9;
                                }
                            }
                    }
                }
            }
        }
    }
    step();
    simp();
}
```

```expect
pass
```
