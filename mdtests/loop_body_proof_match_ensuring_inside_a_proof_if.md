# A rejoined `match` inside a proof `if` keeps the `if` on its path

The loop body splits on a proof `if` whose arms each run to the end of the
iteration. Inside each arm a `match` rejoins through `ensuring`, and a second
`match` after it runs its arms to the end.

The path that leaves the rejoined `match` is still on the enclosing `if`'s
case: the join ends its own two cases, not the ones the proof took to reach
it. Dropping them left the four leaves of this body with no `if` to be
grouped under when their certificates were merged, and the body was refused
as having "incompatible next proof `match`".

```c filename=loop_body_proof_match_ensuring_inside_a_proof_if.c
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
verifying "loop_body_proof_match_ensuring_inside_a_proof_if.c";

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
            if i < 5 {
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
                match c.model {
                    Sign::Neg(w) => {
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
                    },
                    Sign::Pos(w) => {
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
                    },
                }
            } else {
                match c.model ensuring {
                    owns c: cell(node);
                } {
                    Sign::Neg(value2) => {
                        unfold(c);
                        let c = fold(cell(node), { model: Sign::Neg(value2) });
                    },
                    Sign::Pos(value2) => {
                        unfold(c);
                        let c = fold(cell(node), { model: Sign::Pos(value2) });
                    },
                }
                match c.model {
                    Sign::Neg(w2) => {
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
                    },
                    Sign::Pos(w2) => {
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
                    },
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
