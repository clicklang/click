# An open scope can fulfill one declared consumption before return

An explicit member consumption inside an open control scope lowers Count once.
Closing restores the counter invariant at that new Count; reopening the control
permits a later read without consuming again. Nested calls and either branch
preserve that effect. The caller starts with empty authority, creates three
members, calls the contribution helper twice, and proves exact two before
consuming the final member and retiring authority. C source is unchanged.

```c filename=early_consumption.c
struct counter { unsigned int value; };
unsigned int contribute_early(struct counter *p) {
    p->value = p->value + 1u;
    return p->value;
}
unsigned int read_current(struct counter *p) { return p->value; }
unsigned int contribute_nested(struct counter *p) {
    p->value = p->value + 1u;
    return read_current(p);
}
unsigned int contribute_branch(struct counter *p, int report) {
    p->value = p->value + 1u;
    if (report) return p->value;
    return 0u;
}
unsigned int sequential_early(struct counter *p) {
    p->value = 0u;
    contribute_early(p);
    contribute_early(p);
    return p->value;
}
```

```click
verifying "early_consumption.c";
authorized resource remaining(p: struct counter*) {}
resource storage(p: struct counter*) {
    owns p->value;
    owns authority(remaining(p));
    fact count(remaining(p)) == 0;
}
resource control(p: struct counter*) {
    owns authority(remaining(p));
    owns p->value;
    fact count(remaining(p)) <= 3;
    fact p->value == 3 - count(remaining(p));
}
uint32 contribute_early(struct counter* p) {
    owns control(p);
    consumes remaining(p);
    requires count(remaining(p)) > 1;
    ensures count(remaining(p)) == old(count(remaining(p))) - 1;
    ensures p->value == old(p->value) + 1;
} by {
    open(control(p)) {
        have to_integer(count(remaining(p))) <= 3 by {
            assumption();
        }
    }
    open(control(p)) {
        have (to_integer(count(remaining(p))) - 1) >= 1 by {
            arithmetic_certificate {
                premise 0: to_integer(count(remaining(p))) > 1 => to_integer(count(remaining(p))) >
                    1;
                conclusion 0;
            }
        }
        have (to_integer(count(remaining(p))) - 1) <= 3 by {
            arithmetic_certificate {
                premise 0: to_integer(count(remaining(p))) <= 3 => to_integer(count(remaining(p)))
                    <= 3;
                trivial => -1 <= 0;
                add 0, 1 => (to_integer(count(remaining(p))) + -1) <= (3 + 0);
                conclusion 2;
            }
        }
        unfold(remaining(p));
        step();
        have to_integer(p->value) == (3 - to_integer(count(remaining(p)))) by {
            have 0 <= (to_integer(old(p->value)) + 1) by {
                arithmetic_certificate {
                    negated_goal => (to_integer(old(p->value)) + 1) < 0;
                    premise 0: at(function.entry, (to_integer(count(remaining(p))) - 1)) <=
                        at(function.entry, 3) => at(function.entry, (to_integer(count(remaining(p)))
                        - 1)) <= at(function.entry, 3);
                    premise 1: at(function.entry, to_integer(p->value)) == at(function.entry, (3 -
                        to_integer(count(remaining(p))))) => at(function.entry,
                        to_integer(p->value)) == at(function.entry, (3 -
                        to_integer(count(remaining(p)))));
                    less_equal_from_equal 2 reverse => at(function.entry, (3 -
                        to_integer(count(remaining(p))))) <= at(function.entry,
                        to_integer(p->value));
                    add 0, 1 => (to_integer(old(p->value)) + 1 + at(function.entry,
                        (to_integer(count(remaining(p))) - 1))) < (0 + at(function.entry, 3));
                    add 4, 3 => (to_integer(old(p->value)) + 1 + at(function.entry,
                        (to_integer(count(remaining(p))) - 1)) + at(function.entry, (3 -
                        to_integer(count(remaining(p)))))) < (0 + at(function.entry, 3) +
                        at(function.entry, to_integer(p->value)));
                    conclusion 5;
                }
            }
            have (to_integer(old(p->value)) + 1) <= 4294967295 by {
                arithmetic_certificate {
                    negated_goal => 4294967295 < (to_integer(old(p->value)) + 1);
                    premise 0: at(function.entry, (to_integer(count(remaining(p))) - 1)) >=
                        at(function.entry, 1) => at(function.entry, (to_integer(count(remaining(p)))
                        - 1)) >= at(function.entry, 1);
                    premise 1: at(function.entry, to_integer(p->value)) == at(function.entry, (3 -
                        to_integer(count(remaining(p))))) => at(function.entry,
                        to_integer(p->value)) == at(function.entry, (3 -
                        to_integer(count(remaining(p)))));
                    less_equal_from_equal 2 => at(function.entry, to_integer(p->value)) <=
                        at(function.entry, (3 - to_integer(count(remaining(p)))));
                    add 0, 1 => (4294967295 + at(function.entry, 1)) < (to_integer(old(p->value)) +
                        1 + at(function.entry, (to_integer(count(remaining(p))) - 1)));
                    add 4, 3 => (4294967295 + at(function.entry, 1) + at(function.entry,
                        to_integer(p->value))) < (to_integer(old(p->value)) + 1 + at(function.entry,
                        (to_integer(count(remaining(p))) - 1)) + at(function.entry, (3 -
                        to_integer(count(remaining(p))))));
                    conclusion 5;
                }
            }
            have to_integer(p->value) == (to_integer(old(p->value)) + 1) by {
                arithmetic_certificate rules {
                    premise 0: 0 <= (to_integer(old(p->value)) + 1) => 0 <=
                        (to_integer(old(p->value)) + 1);
                    premise 1: (to_integer(old(p->value)) + 1) <= 4294967295 =>
                        (to_integer(old(p->value)) + 1) <= 4294967295;
                    integer_operation_identity bounds [0, 1] => to_integer(p->value) ==
                        (to_integer(old(p->value)) + 1);
                    conclusion 0;
                }
            }
            have -2147483648 <= (to_integer(old(count(remaining(p)))) - 1) by {
                arithmetic_certificate {
                    negated_goal => (to_integer(old(count(remaining(p)))) - 1) < -2147483648;
                    premise 0: at(function.entry, (to_integer(count(remaining(p))) - 1)) >=
                        at(function.entry, 1) => at(function.entry, (to_integer(count(remaining(p)))
                        - 1)) >= at(function.entry, 1);
                    add 0, 1 => ((to_integer(old(count(remaining(p)))) - 1) + at(function.entry, 1))
                        < (-2147483648 + at(function.entry, (to_integer(count(remaining(p))) - 1)));
                    conclusion 2;
                }
            }
            have (to_integer(old(count(remaining(p)))) - 1) <= 2147483647 by {
                arithmetic_certificate {
                    negated_goal => 2147483647 < (to_integer(old(count(remaining(p)))) - 1);
                    premise 0: at(function.entry, (to_integer(count(remaining(p))) - 1)) <=
                        at(function.entry, 3) => at(function.entry, (to_integer(count(remaining(p)))
                        - 1)) <= at(function.entry, 3);
                    add 0, 1 => (2147483647 + at(function.entry, (to_integer(count(remaining(p))) -
                        1))) < ((to_integer(old(count(remaining(p)))) - 1) + at(function.entry, 3));
                    conclusion 2;
                }
            }
            have to_integer(count(remaining(p))) == (to_integer(old(count(remaining(p)))) - 1) by {
                arithmetic_certificate rules {
                    premise 0: -2147483648 <= (to_integer(old(count(remaining(p)))) - 1) =>
                        -2147483648 <= (to_integer(old(count(remaining(p)))) - 1);
                    premise 1: (to_integer(old(count(remaining(p)))) - 1) <= 2147483647 =>
                        (to_integer(old(count(remaining(p)))) - 1) <= 2147483647;
                    integer_operation_identity bounds [0, 1] => to_integer(count(remaining(p))) ==
                        (to_integer(old(count(remaining(p)))) - 1);
                    conclusion 0;
                }
            }
            have to_integer(p->value) <= (3 - to_integer(count(remaining(p)))) by {
                arithmetic_certificate {
                    negated_goal => (3 - to_integer(count(remaining(p)))) < to_integer(p->value);
                    premise 0: at(function.entry, to_integer(p->value)) == at(function.entry, (3 -
                        to_integer(count(remaining(p))))) => at(function.entry,
                        to_integer(p->value)) == at(function.entry, (3 -
                        to_integer(count(remaining(p)))));
                    less_equal_from_equal 1 => at(function.entry, to_integer(p->value)) <=
                        at(function.entry, (3 - to_integer(count(remaining(p)))));
                    premise 1: to_integer(count(remaining(p))) ==
                        (to_integer(old(count(remaining(p)))) - 1) =>
                        to_integer(count(remaining(p))) == (to_integer(old(count(remaining(p)))) -
                        1);
                    less_equal_from_equal 3 => to_integer(count(remaining(p))) <=
                        (to_integer(old(count(remaining(p)))) - 1);
                    premise 2: to_integer(p->value) == (to_integer(old(p->value)) + 1) =>
                        to_integer(p->value) == (to_integer(old(p->value)) + 1);
                    less_equal_from_equal 5 => to_integer(p->value) <= (to_integer(old(p->value)) +
                        1);
                    add 0, 2 => ((3 - to_integer(count(remaining(p)))) + at(function.entry,
                        to_integer(p->value))) < (to_integer(p->value) + at(function.entry, (3 -
                        to_integer(count(remaining(p))))));
                    add 7, 4 => ((3 - to_integer(count(remaining(p)))) + at(function.entry,
                        to_integer(p->value)) + to_integer(count(remaining(p)))) <
                        (to_integer(p->value) + at(function.entry, (3 -
                        to_integer(count(remaining(p))))) + (to_integer(old(count(remaining(p)))) -
                        1));
                    add 8, 6 => ((3 - to_integer(count(remaining(p)))) + at(function.entry,
                        to_integer(p->value)) + to_integer(count(remaining(p))) +
                        to_integer(p->value)) < (to_integer(p->value) + at(function.entry, (3 -
                        to_integer(count(remaining(p))))) + (to_integer(old(count(remaining(p)))) -
                        1) + (to_integer(old(p->value)) + 1));
                    conclusion 9;
                }
            }
            have (3 - to_integer(count(remaining(p)))) <= to_integer(p->value) by {
                arithmetic_certificate {
                    negated_goal => to_integer(p->value) < (3 - to_integer(count(remaining(p))));
                    premise 0: at(function.entry, to_integer(p->value)) == at(function.entry, (3 -
                        to_integer(count(remaining(p))))) => at(function.entry,
                        to_integer(p->value)) == at(function.entry, (3 -
                        to_integer(count(remaining(p)))));
                    less_equal_from_equal 1 reverse => at(function.entry, (3 -
                        to_integer(count(remaining(p))))) <= at(function.entry,
                        to_integer(p->value));
                    premise 1: to_integer(count(remaining(p))) ==
                        (to_integer(old(count(remaining(p)))) - 1) =>
                        to_integer(count(remaining(p))) == (to_integer(old(count(remaining(p)))) -
                        1);
                    less_equal_from_equal 3 reverse => (to_integer(old(count(remaining(p)))) - 1) <=
                        to_integer(count(remaining(p)));
                    premise 2: to_integer(p->value) == (to_integer(old(p->value)) + 1) =>
                        to_integer(p->value) == (to_integer(old(p->value)) + 1);
                    less_equal_from_equal 5 reverse => (to_integer(old(p->value)) + 1) <=
                        to_integer(p->value);
                    add 0, 2 => (to_integer(p->value) + at(function.entry, (3 -
                        to_integer(count(remaining(p)))))) < ((3 - to_integer(count(remaining(p))))
                        + at(function.entry, to_integer(p->value)));
                    add 7, 4 => (to_integer(p->value) + at(function.entry, (3 -
                        to_integer(count(remaining(p))))) + (to_integer(old(count(remaining(p)))) -
                        1)) < ((3 - to_integer(count(remaining(p)))) + at(function.entry,
                        to_integer(p->value)) + to_integer(count(remaining(p))));
                    add 8, 6 => (to_integer(p->value) + at(function.entry, (3 -
                        to_integer(count(remaining(p))))) + (to_integer(old(count(remaining(p)))) -
                        1) + (to_integer(old(p->value)) + 1)) < ((3 -
                        to_integer(count(remaining(p)))) + at(function.entry, to_integer(p->value))
                        + to_integer(count(remaining(p))) + to_integer(p->value));
                    conclusion 9;
                }
            }
            arithmetic_certificate {
                premise 0: to_integer(p->value) <= (3 - to_integer(count(remaining(p)))) =>
                    to_integer(p->value) <= (3 - to_integer(count(remaining(p))));
                premise 1: (3 - to_integer(count(remaining(p)))) <= to_integer(p->value) => (3 -
                    to_integer(count(remaining(p)))) <= to_integer(p->value);
                equal_from_bounds 0, 1 => to_integer(p->value) == (3 -
                    to_integer(count(remaining(p))));
                conclusion 2;
            }
        }
    }
    open(control(p)) {
        step();
    }
    assumption();
    have to_integer(count(remaining(p))) == (to_integer(old(count(remaining(p)))) - 1) by {
        have -2147483648 <= (to_integer(old(count(remaining(p)))) - 1) by {
            arithmetic_certificate {
                negated_goal => (to_integer(old(count(remaining(p)))) - 1) < -2147483648;
                premise 0: at(function.entry, (to_integer(count(remaining(p))) - 1)) >=
                    at(function.entry, 1) => at(function.entry, (to_integer(count(remaining(p))) -
                    1)) >= at(function.entry, 1);
                add 0, 1 => ((to_integer(old(count(remaining(p)))) - 1) + at(function.entry, 1)) <
                    (-2147483648 + at(function.entry, (to_integer(count(remaining(p))) - 1)));
                conclusion 2;
            }
        }
        have (to_integer(old(count(remaining(p)))) - 1) <= 2147483647 by {
            arithmetic_certificate {
                negated_goal => 2147483647 < (to_integer(old(count(remaining(p)))) - 1);
                premise 0: at(function.entry, (to_integer(count(remaining(p))) - 1)) <=
                    at(function.entry, 3) => at(function.entry, (to_integer(count(remaining(p))) -
                    1)) <= at(function.entry, 3);
                add 0, 1 => (2147483647 + at(function.entry, (to_integer(count(remaining(p))) - 1)))
                    < ((to_integer(old(count(remaining(p)))) - 1) + at(function.entry, 3));
                conclusion 2;
            }
        }
        have to_integer(count(remaining(p))) == (to_integer(old(count(remaining(p)))) - 1) by {
            arithmetic_certificate rules {
                premise 0: -2147483648 <= (to_integer(old(count(remaining(p)))) - 1) => -2147483648
                    <= (to_integer(old(count(remaining(p)))) - 1);
                premise 1: (to_integer(old(count(remaining(p)))) - 1) <= 2147483647 =>
                    (to_integer(old(count(remaining(p)))) - 1) <= 2147483647;
                integer_operation_identity bounds [0, 1] => to_integer(count(remaining(p))) ==
                    (to_integer(old(count(remaining(p)))) - 1);
                conclusion 0;
            }
        }
        assumption();
    }
    have to_integer(p->value) == (to_integer(old(p->value)) + 1) by {
        rewrite(at(function.entry, to_integer(p->value)) == at(function.entry, (3 - to_integer(count(remaining(p))))));
        rewrite(to_integer(p->value) == (3 - to_integer(count(remaining(p)))));
        rewrite(to_integer(count(remaining(p))) == (to_integer(old(count(remaining(p)))) - 1));
        normalize();
    }
    assumption();
    assumption();
}
uint32 read_current(struct counter* p) {
    owns control(p);
} by {
    open(control(p)) {
        step();
    }
    assumption();
}
uint32 contribute_nested(struct counter* p) {
    owns control(p);
    consumes remaining(p);
    requires count(remaining(p)) > 1;
    ensures count(remaining(p)) == old(count(remaining(p))) - 1;
    ensures p->value == old(p->value) + 1;
} by {
    open(control(p)) {
        have (to_integer(count(remaining(p))) - 1) >= 1 by {
            arithmetic_certificate {
                premise 0: to_integer(count(remaining(p))) > 1 => to_integer(count(remaining(p))) >
                    1;
                conclusion 0;
            }
        }
        have (to_integer(count(remaining(p))) - 1) <= 3 by {
            arithmetic_certificate {
                premise 0: to_integer(count(remaining(p))) <= 3 => to_integer(count(remaining(p)))
                    <= 3;
                trivial => -1 <= 0;
                add 0, 1 => (to_integer(count(remaining(p))) + -1) <= (3 + 0);
                conclusion 2;
            }
        }
        unfold(remaining(p));
        step();
        have to_integer(p->value) == (3 - to_integer(count(remaining(p)))) by {
            have 0 <= (to_integer(old(p->value)) + 1) by {
                arithmetic_certificate {
                    negated_goal => (to_integer(old(p->value)) + 1) < 0;
                    premise 0: at(function.entry, (to_integer(count(remaining(p))) - 1)) <=
                        at(function.entry, 3) => at(function.entry, (to_integer(count(remaining(p)))
                        - 1)) <= at(function.entry, 3);
                    premise 1: at(function.entry, to_integer(p->value)) == at(function.entry, (3 -
                        to_integer(count(remaining(p))))) => at(function.entry,
                        to_integer(p->value)) == at(function.entry, (3 -
                        to_integer(count(remaining(p)))));
                    less_equal_from_equal 2 reverse => at(function.entry, (3 -
                        to_integer(count(remaining(p))))) <= at(function.entry,
                        to_integer(p->value));
                    add 0, 1 => (to_integer(old(p->value)) + 1 + at(function.entry,
                        (to_integer(count(remaining(p))) - 1))) < (0 + at(function.entry, 3));
                    add 4, 3 => (to_integer(old(p->value)) + 1 + at(function.entry,
                        (to_integer(count(remaining(p))) - 1)) + at(function.entry, (3 -
                        to_integer(count(remaining(p)))))) < (0 + at(function.entry, 3) +
                        at(function.entry, to_integer(p->value)));
                    conclusion 5;
                }
            }
            have (to_integer(old(p->value)) + 1) <= 4294967295 by {
                arithmetic_certificate {
                    negated_goal => 4294967295 < (to_integer(old(p->value)) + 1);
                    premise 0: at(function.entry, (to_integer(count(remaining(p))) - 1)) >=
                        at(function.entry, 1) => at(function.entry, (to_integer(count(remaining(p)))
                        - 1)) >= at(function.entry, 1);
                    premise 1: at(function.entry, to_integer(p->value)) == at(function.entry, (3 -
                        to_integer(count(remaining(p))))) => at(function.entry,
                        to_integer(p->value)) == at(function.entry, (3 -
                        to_integer(count(remaining(p)))));
                    less_equal_from_equal 2 => at(function.entry, to_integer(p->value)) <=
                        at(function.entry, (3 - to_integer(count(remaining(p)))));
                    add 0, 1 => (4294967295 + at(function.entry, 1)) < (to_integer(old(p->value)) +
                        1 + at(function.entry, (to_integer(count(remaining(p))) - 1)));
                    add 4, 3 => (4294967295 + at(function.entry, 1) + at(function.entry,
                        to_integer(p->value))) < (to_integer(old(p->value)) + 1 + at(function.entry,
                        (to_integer(count(remaining(p))) - 1)) + at(function.entry, (3 -
                        to_integer(count(remaining(p))))));
                    conclusion 5;
                }
            }
            have to_integer(p->value) == (to_integer(old(p->value)) + 1) by {
                arithmetic_certificate rules {
                    premise 0: 0 <= (to_integer(old(p->value)) + 1) => 0 <=
                        (to_integer(old(p->value)) + 1);
                    premise 1: (to_integer(old(p->value)) + 1) <= 4294967295 =>
                        (to_integer(old(p->value)) + 1) <= 4294967295;
                    integer_operation_identity bounds [0, 1] => to_integer(p->value) ==
                        (to_integer(old(p->value)) + 1);
                    conclusion 0;
                }
            }
            have -2147483648 <= (to_integer(old(count(remaining(p)))) - 1) by {
                arithmetic_certificate {
                    negated_goal => (to_integer(old(count(remaining(p)))) - 1) < -2147483648;
                    premise 0: at(function.entry, (to_integer(count(remaining(p))) - 1)) >=
                        at(function.entry, 1) => at(function.entry, (to_integer(count(remaining(p)))
                        - 1)) >= at(function.entry, 1);
                    add 0, 1 => ((to_integer(old(count(remaining(p)))) - 1) + at(function.entry, 1))
                        < (-2147483648 + at(function.entry, (to_integer(count(remaining(p))) - 1)));
                    conclusion 2;
                }
            }
            have (to_integer(old(count(remaining(p)))) - 1) <= 2147483647 by {
                arithmetic_certificate {
                    negated_goal => 2147483647 < (to_integer(old(count(remaining(p)))) - 1);
                    premise 0: at(function.entry, (to_integer(count(remaining(p))) - 1)) <=
                        at(function.entry, 3) => at(function.entry, (to_integer(count(remaining(p)))
                        - 1)) <= at(function.entry, 3);
                    add 0, 1 => (2147483647 + at(function.entry, (to_integer(count(remaining(p))) -
                        1))) < ((to_integer(old(count(remaining(p)))) - 1) + at(function.entry, 3));
                    conclusion 2;
                }
            }
            have to_integer(count(remaining(p))) == (to_integer(old(count(remaining(p)))) - 1) by {
                arithmetic_certificate rules {
                    premise 0: -2147483648 <= (to_integer(old(count(remaining(p)))) - 1) =>
                        -2147483648 <= (to_integer(old(count(remaining(p)))) - 1);
                    premise 1: (to_integer(old(count(remaining(p)))) - 1) <= 2147483647 =>
                        (to_integer(old(count(remaining(p)))) - 1) <= 2147483647;
                    integer_operation_identity bounds [0, 1] => to_integer(count(remaining(p))) ==
                        (to_integer(old(count(remaining(p)))) - 1);
                    conclusion 0;
                }
            }
            have to_integer(p->value) <= (3 - to_integer(count(remaining(p)))) by {
                arithmetic_certificate {
                    negated_goal => (3 - to_integer(count(remaining(p)))) < to_integer(p->value);
                    premise 0: at(function.entry, to_integer(p->value)) == at(function.entry, (3 -
                        to_integer(count(remaining(p))))) => at(function.entry,
                        to_integer(p->value)) == at(function.entry, (3 -
                        to_integer(count(remaining(p)))));
                    less_equal_from_equal 1 => at(function.entry, to_integer(p->value)) <=
                        at(function.entry, (3 - to_integer(count(remaining(p)))));
                    premise 1: to_integer(count(remaining(p))) ==
                        (to_integer(old(count(remaining(p)))) - 1) =>
                        to_integer(count(remaining(p))) == (to_integer(old(count(remaining(p)))) -
                        1);
                    less_equal_from_equal 3 => to_integer(count(remaining(p))) <=
                        (to_integer(old(count(remaining(p)))) - 1);
                    premise 2: to_integer(p->value) == (to_integer(old(p->value)) + 1) =>
                        to_integer(p->value) == (to_integer(old(p->value)) + 1);
                    less_equal_from_equal 5 => to_integer(p->value) <= (to_integer(old(p->value)) +
                        1);
                    add 0, 2 => ((3 - to_integer(count(remaining(p)))) + at(function.entry,
                        to_integer(p->value))) < (to_integer(p->value) + at(function.entry, (3 -
                        to_integer(count(remaining(p))))));
                    add 7, 4 => ((3 - to_integer(count(remaining(p)))) + at(function.entry,
                        to_integer(p->value)) + to_integer(count(remaining(p)))) <
                        (to_integer(p->value) + at(function.entry, (3 -
                        to_integer(count(remaining(p))))) + (to_integer(old(count(remaining(p)))) -
                        1));
                    add 8, 6 => ((3 - to_integer(count(remaining(p)))) + at(function.entry,
                        to_integer(p->value)) + to_integer(count(remaining(p))) +
                        to_integer(p->value)) < (to_integer(p->value) + at(function.entry, (3 -
                        to_integer(count(remaining(p))))) + (to_integer(old(count(remaining(p)))) -
                        1) + (to_integer(old(p->value)) + 1));
                    conclusion 9;
                }
            }
            have (3 - to_integer(count(remaining(p)))) <= to_integer(p->value) by {
                arithmetic_certificate {
                    negated_goal => to_integer(p->value) < (3 - to_integer(count(remaining(p))));
                    premise 0: at(function.entry, to_integer(p->value)) == at(function.entry, (3 -
                        to_integer(count(remaining(p))))) => at(function.entry,
                        to_integer(p->value)) == at(function.entry, (3 -
                        to_integer(count(remaining(p)))));
                    less_equal_from_equal 1 reverse => at(function.entry, (3 -
                        to_integer(count(remaining(p))))) <= at(function.entry,
                        to_integer(p->value));
                    premise 1: to_integer(count(remaining(p))) ==
                        (to_integer(old(count(remaining(p)))) - 1) =>
                        to_integer(count(remaining(p))) == (to_integer(old(count(remaining(p)))) -
                        1);
                    less_equal_from_equal 3 reverse => (to_integer(old(count(remaining(p)))) - 1) <=
                        to_integer(count(remaining(p)));
                    premise 2: to_integer(p->value) == (to_integer(old(p->value)) + 1) =>
                        to_integer(p->value) == (to_integer(old(p->value)) + 1);
                    less_equal_from_equal 5 reverse => (to_integer(old(p->value)) + 1) <=
                        to_integer(p->value);
                    add 0, 2 => (to_integer(p->value) + at(function.entry, (3 -
                        to_integer(count(remaining(p)))))) < ((3 - to_integer(count(remaining(p))))
                        + at(function.entry, to_integer(p->value)));
                    add 7, 4 => (to_integer(p->value) + at(function.entry, (3 -
                        to_integer(count(remaining(p))))) + (to_integer(old(count(remaining(p)))) -
                        1)) < ((3 - to_integer(count(remaining(p)))) + at(function.entry,
                        to_integer(p->value)) + to_integer(count(remaining(p))));
                    add 8, 6 => (to_integer(p->value) + at(function.entry, (3 -
                        to_integer(count(remaining(p))))) + (to_integer(old(count(remaining(p)))) -
                        1) + (to_integer(old(p->value)) + 1)) < ((3 -
                        to_integer(count(remaining(p)))) + at(function.entry, to_integer(p->value))
                        + to_integer(count(remaining(p))) + to_integer(p->value));
                    conclusion 9;
                }
            }
            arithmetic_certificate {
                premise 0: to_integer(p->value) <= (3 - to_integer(count(remaining(p)))) =>
                    to_integer(p->value) <= (3 - to_integer(count(remaining(p))));
                premise 1: (3 - to_integer(count(remaining(p)))) <= to_integer(p->value) => (3 -
                    to_integer(count(remaining(p)))) <= to_integer(p->value);
                equal_from_bounds 0, 1 => to_integer(p->value) == (3 -
                    to_integer(count(remaining(p))));
                conclusion 2;
            }
        }
    }
    step();
    open(control(p)) {
        have to_integer(p->value) == (to_integer(old(p->value)) + 1) by {
            have to_integer(p->value) <= (to_integer(old(p->value)) + 1) by {
                have -2147483648 <= (to_integer(old(count(remaining(p)))) - 1) by {
                    arithmetic_certificate {
                        negated_goal => (to_integer(old(count(remaining(p)))) - 1) < -2147483648;
                        premise 0: at(function.entry, (to_integer(count(remaining(p))) - 1)) >=
                            at(function.entry, 1) => at(function.entry,
                            (to_integer(count(remaining(p))) - 1)) >= at(function.entry, 1);
                        add 0, 1 => ((to_integer(old(count(remaining(p)))) - 1) + at(function.entry,
                            1)) < (-2147483648 + at(function.entry, (to_integer(count(remaining(p)))
                            - 1)));
                        conclusion 2;
                    }
                }
                have (to_integer(old(count(remaining(p)))) - 1) <= 2147483647 by {
                    arithmetic_certificate {
                        negated_goal => 2147483647 < (to_integer(old(count(remaining(p)))) - 1);
                        premise 0: at(function.entry, (to_integer(count(remaining(p))) - 1)) <=
                            at(function.entry, 3) => at(function.entry,
                            (to_integer(count(remaining(p))) - 1)) <= at(function.entry, 3);
                        add 0, 1 => (2147483647 + at(function.entry,
                            (to_integer(count(remaining(p))) - 1))) <
                            ((to_integer(old(count(remaining(p)))) - 1) + at(function.entry, 3));
                        conclusion 2;
                    }
                }
                have to_integer(count(remaining(p))) == (to_integer(old(count(remaining(p)))) - 1) by {
                    arithmetic_certificate rules {
                        premise 0: -2147483648 <= (to_integer(old(count(remaining(p)))) - 1) =>
                            -2147483648 <= (to_integer(old(count(remaining(p)))) - 1);
                        premise 1: (to_integer(old(count(remaining(p)))) - 1) <= 2147483647 =>
                            (to_integer(old(count(remaining(p)))) - 1) <= 2147483647;
                        integer_operation_identity bounds [0, 1] => to_integer(count(remaining(p)))
                            == (to_integer(old(count(remaining(p)))) - 1);
                        conclusion 0;
                    }
                }
                arithmetic_certificate {
                    negated_goal => (to_integer(old(p->value)) + 1) < to_integer(p->value);
                    premise 0: at(function.entry, to_integer(p->value)) == at(function.entry, (3 -
                        to_integer(count(remaining(p))))) => at(function.entry,
                        to_integer(p->value)) == at(function.entry, (3 -
                        to_integer(count(remaining(p)))));
                    less_equal_from_equal 1 reverse => at(function.entry, (3 -
                        to_integer(count(remaining(p))))) <= at(function.entry,
                        to_integer(p->value));
                    premise 1: to_integer(count(remaining(p))) ==
                        (to_integer(old(count(remaining(p)))) - 1) =>
                        to_integer(count(remaining(p))) == (to_integer(old(count(remaining(p)))) -
                        1);
                    less_equal_from_equal 3 reverse => (to_integer(old(count(remaining(p)))) - 1) <=
                        to_integer(count(remaining(p)));
                    premise 2: to_integer(p->value) == (3 - to_integer(count(remaining(p)))) =>
                        to_integer(p->value) == (3 - to_integer(count(remaining(p))));
                    less_equal_from_equal 5 => to_integer(p->value) <= (3 -
                        to_integer(count(remaining(p))));
                    add 0, 2 => (to_integer(old(p->value)) + 1 + at(function.entry, (3 -
                        to_integer(count(remaining(p)))))) < (to_integer(p->value) +
                        at(function.entry, to_integer(p->value)));
                    add 7, 4 => (to_integer(old(p->value)) + 1 + at(function.entry, (3 -
                        to_integer(count(remaining(p))))) + (to_integer(old(count(remaining(p)))) -
                        1)) < (to_integer(p->value) + at(function.entry, to_integer(p->value)) +
                        to_integer(count(remaining(p))));
                    add 8, 6 => (to_integer(old(p->value)) + 1 + at(function.entry, (3 -
                        to_integer(count(remaining(p))))) + (to_integer(old(count(remaining(p)))) -
                        1) + to_integer(p->value)) < (to_integer(p->value) + at(function.entry,
                        to_integer(p->value)) + to_integer(count(remaining(p))) + (3 -
                        to_integer(count(remaining(p)))));
                    conclusion 9;
                }
            }
            have (to_integer(old(p->value)) + 1) <= to_integer(p->value) by {
                have -2147483648 <= (to_integer(old(count(remaining(p)))) - 1) by {
                    arithmetic_certificate {
                        negated_goal => (to_integer(old(count(remaining(p)))) - 1) < -2147483648;
                        premise 0: at(function.entry, (to_integer(count(remaining(p))) - 1)) >=
                            at(function.entry, 1) => at(function.entry,
                            (to_integer(count(remaining(p))) - 1)) >= at(function.entry, 1);
                        add 0, 1 => ((to_integer(old(count(remaining(p)))) - 1) + at(function.entry,
                            1)) < (-2147483648 + at(function.entry, (to_integer(count(remaining(p)))
                            - 1)));
                        conclusion 2;
                    }
                }
                have (to_integer(old(count(remaining(p)))) - 1) <= 2147483647 by {
                    arithmetic_certificate {
                        negated_goal => 2147483647 < (to_integer(old(count(remaining(p)))) - 1);
                        premise 0: at(function.entry, (to_integer(count(remaining(p))) - 1)) <=
                            at(function.entry, 3) => at(function.entry,
                            (to_integer(count(remaining(p))) - 1)) <= at(function.entry, 3);
                        add 0, 1 => (2147483647 + at(function.entry,
                            (to_integer(count(remaining(p))) - 1))) <
                            ((to_integer(old(count(remaining(p)))) - 1) + at(function.entry, 3));
                        conclusion 2;
                    }
                }
                have to_integer(count(remaining(p))) == (to_integer(old(count(remaining(p)))) - 1) by {
                    arithmetic_certificate rules {
                        premise 0: -2147483648 <= (to_integer(old(count(remaining(p)))) - 1) =>
                            -2147483648 <= (to_integer(old(count(remaining(p)))) - 1);
                        premise 1: (to_integer(old(count(remaining(p)))) - 1) <= 2147483647 =>
                            (to_integer(old(count(remaining(p)))) - 1) <= 2147483647;
                        integer_operation_identity bounds [0, 1] => to_integer(count(remaining(p)))
                            == (to_integer(old(count(remaining(p)))) - 1);
                        conclusion 0;
                    }
                }
                arithmetic_certificate {
                    negated_goal => to_integer(p->value) < (to_integer(old(p->value)) + 1);
                    premise 0: at(function.entry, to_integer(p->value)) == at(function.entry, (3 -
                        to_integer(count(remaining(p))))) => at(function.entry,
                        to_integer(p->value)) == at(function.entry, (3 -
                        to_integer(count(remaining(p)))));
                    less_equal_from_equal 1 => at(function.entry, to_integer(p->value)) <=
                        at(function.entry, (3 - to_integer(count(remaining(p)))));
                    premise 1: to_integer(count(remaining(p))) ==
                        (to_integer(old(count(remaining(p)))) - 1) =>
                        to_integer(count(remaining(p))) == (to_integer(old(count(remaining(p)))) -
                        1);
                    less_equal_from_equal 3 => to_integer(count(remaining(p))) <=
                        (to_integer(old(count(remaining(p)))) - 1);
                    premise 2: to_integer(p->value) == (3 - to_integer(count(remaining(p)))) =>
                        to_integer(p->value) == (3 - to_integer(count(remaining(p))));
                    less_equal_from_equal 5 reverse => (3 - to_integer(count(remaining(p)))) <=
                        to_integer(p->value);
                    add 0, 2 => (to_integer(p->value) + at(function.entry, to_integer(p->value))) <
                        (to_integer(old(p->value)) + 1 + at(function.entry, (3 -
                        to_integer(count(remaining(p))))));
                    add 7, 4 => (to_integer(p->value) + at(function.entry, to_integer(p->value)) +
                        to_integer(count(remaining(p)))) < (to_integer(old(p->value)) + 1 +
                        at(function.entry, (3 - to_integer(count(remaining(p))))) +
                        (to_integer(old(count(remaining(p)))) - 1));
                    add 8, 6 => (to_integer(p->value) + at(function.entry, to_integer(p->value)) +
                        to_integer(count(remaining(p))) + (3 - to_integer(count(remaining(p))))) <
                        (to_integer(old(p->value)) + 1 + at(function.entry, (3 -
                        to_integer(count(remaining(p))))) + (to_integer(old(count(remaining(p)))) -
                        1) + to_integer(p->value));
                    conclusion 9;
                }
            }
            arithmetic_certificate {
                premise 0: to_integer(p->value) <= (to_integer(old(p->value)) + 1) =>
                    to_integer(p->value) <= (to_integer(old(p->value)) + 1);
                premise 1: (to_integer(old(p->value)) + 1) <= to_integer(p->value) =>
                    (to_integer(old(p->value)) + 1) <= to_integer(p->value);
                equal_from_bounds 0, 1 => to_integer(p->value) == (to_integer(old(p->value)) + 1);
                conclusion 2;
            }
        }
    }
    step();
    assumption();
    have to_integer(count(remaining(p))) == (to_integer(old(count(remaining(p)))) - 1) by {
        have to_integer(count(remaining(p))) <= (to_integer(old(count(remaining(p)))) - 1) by {
            arithmetic_certificate {
                negated_goal => (to_integer(old(count(remaining(p)))) - 1) <
                    to_integer(count(remaining(p)));
                premise 0: at(function.entry, to_integer(p->value)) == at(function.entry, (3 -
                    to_integer(count(remaining(p))))) => at(function.entry, to_integer(p->value)) ==
                    at(function.entry, (3 - to_integer(count(remaining(p)))));
                less_equal_from_equal 1 reverse => at(function.entry, (3 -
                    to_integer(count(remaining(p))))) <= at(function.entry, to_integer(p->value));
                premise 1: to_integer(p->value) == (3 - to_integer(count(remaining(p)))) =>
                    to_integer(p->value) == (3 - to_integer(count(remaining(p))));
                less_equal_from_equal 3 => to_integer(p->value) <= (3 -
                    to_integer(count(remaining(p))));
                premise 2: to_integer(p->value) == (to_integer(old(p->value)) + 1) =>
                    to_integer(p->value) == (to_integer(old(p->value)) + 1);
                less_equal_from_equal 5 reverse => (to_integer(old(p->value)) + 1) <=
                    to_integer(p->value);
                add 0, 2 => ((to_integer(old(count(remaining(p)))) - 1) + at(function.entry, (3 -
                    to_integer(count(remaining(p)))))) < (to_integer(count(remaining(p))) +
                    at(function.entry, to_integer(p->value)));
                add 7, 4 => ((to_integer(old(count(remaining(p)))) - 1) + at(function.entry, (3 -
                    to_integer(count(remaining(p))))) + to_integer(p->value)) <
                    (to_integer(count(remaining(p))) + at(function.entry, to_integer(p->value)) + (3
                    - to_integer(count(remaining(p)))));
                add 8, 6 => ((to_integer(old(count(remaining(p)))) - 1) + at(function.entry, (3 -
                    to_integer(count(remaining(p))))) + to_integer(p->value) +
                    (to_integer(old(p->value)) + 1)) < (to_integer(count(remaining(p))) +
                    at(function.entry, to_integer(p->value)) + (3 - to_integer(count(remaining(p))))
                    + to_integer(p->value));
                conclusion 9;
            }
        }
        have (to_integer(old(count(remaining(p)))) - 1) <= to_integer(count(remaining(p))) by {
            arithmetic_certificate {
                negated_goal => to_integer(count(remaining(p))) <
                    (to_integer(old(count(remaining(p)))) - 1);
                premise 0: at(function.entry, to_integer(p->value)) == at(function.entry, (3 -
                    to_integer(count(remaining(p))))) => at(function.entry, to_integer(p->value)) ==
                    at(function.entry, (3 - to_integer(count(remaining(p)))));
                less_equal_from_equal 1 => at(function.entry, to_integer(p->value)) <=
                    at(function.entry, (3 - to_integer(count(remaining(p)))));
                premise 1: to_integer(p->value) == (3 - to_integer(count(remaining(p)))) =>
                    to_integer(p->value) == (3 - to_integer(count(remaining(p))));
                less_equal_from_equal 3 reverse => (3 - to_integer(count(remaining(p)))) <=
                    to_integer(p->value);
                premise 2: to_integer(p->value) == (to_integer(old(p->value)) + 1) =>
                    to_integer(p->value) == (to_integer(old(p->value)) + 1);
                less_equal_from_equal 5 => to_integer(p->value) <= (to_integer(old(p->value)) + 1);
                add 0, 2 => (to_integer(count(remaining(p))) + at(function.entry,
                    to_integer(p->value))) < ((to_integer(old(count(remaining(p)))) - 1) +
                    at(function.entry, (3 - to_integer(count(remaining(p))))));
                add 7, 4 => (to_integer(count(remaining(p))) + at(function.entry,
                    to_integer(p->value)) + (3 - to_integer(count(remaining(p))))) <
                    ((to_integer(old(count(remaining(p)))) - 1) + at(function.entry, (3 -
                    to_integer(count(remaining(p))))) + to_integer(p->value));
                add 8, 6 => (to_integer(count(remaining(p))) + at(function.entry,
                    to_integer(p->value)) + (3 - to_integer(count(remaining(p)))) +
                    to_integer(p->value)) < ((to_integer(old(count(remaining(p)))) - 1) +
                    at(function.entry, (3 - to_integer(count(remaining(p))))) + to_integer(p->value)
                    + (to_integer(old(p->value)) + 1));
                conclusion 9;
            }
        }
        arithmetic_certificate {
            premise 0: to_integer(count(remaining(p))) <= (to_integer(old(count(remaining(p)))) - 1)
                => to_integer(count(remaining(p))) <= (to_integer(old(count(remaining(p)))) - 1);
            premise 1: (to_integer(old(count(remaining(p)))) - 1) <= to_integer(count(remaining(p)))
                => (to_integer(old(count(remaining(p)))) - 1) <= to_integer(count(remaining(p)));
            equal_from_bounds 0, 1 => to_integer(count(remaining(p))) ==
                (to_integer(old(count(remaining(p)))) - 1);
            conclusion 2;
        }
    }
    have to_integer(p->value) == (to_integer(old(p->value)) + 1) by {
        assumption();
    }
    assumption();
    assumption();
}
uint32 contribute_branch(struct counter* p, int32 report) {
    owns control(p);
    consumes remaining(p);
    requires count(remaining(p)) > 1;
    ensures count(remaining(p)) == old(count(remaining(p))) - 1;
    ensures p->value == old(p->value) + 1;
} by {
    open(control(p)) {
        have (to_integer(count(remaining(p))) - 1) >= 1 by {
            arithmetic_certificate {
                premise 0: to_integer(count(remaining(p))) > 1 => to_integer(count(remaining(p))) >
                    1;
                conclusion 0;
            }
        }
        have (to_integer(count(remaining(p))) - 1) <= 3 by {
            arithmetic_certificate {
                premise 0: to_integer(count(remaining(p))) <= 3 => to_integer(count(remaining(p)))
                    <= 3;
                trivial => -1 <= 0;
                add 0, 1 => (to_integer(count(remaining(p))) + -1) <= (3 + 0);
                conclusion 2;
            }
        }
        unfold(remaining(p));
        step();
        have to_integer(p->value) == (3 - to_integer(count(remaining(p)))) by {
            have 0 <= (to_integer(old(p->value)) + 1) by {
                arithmetic_certificate {
                    negated_goal => (to_integer(old(p->value)) + 1) < 0;
                    premise 0: at(function.entry, (to_integer(count(remaining(p))) - 1)) <=
                        at(function.entry, 3) => at(function.entry, (to_integer(count(remaining(p)))
                        - 1)) <= at(function.entry, 3);
                    premise 1: at(function.entry, to_integer(p->value)) == at(function.entry, (3 -
                        to_integer(count(remaining(p))))) => at(function.entry,
                        to_integer(p->value)) == at(function.entry, (3 -
                        to_integer(count(remaining(p)))));
                    less_equal_from_equal 2 reverse => at(function.entry, (3 -
                        to_integer(count(remaining(p))))) <= at(function.entry,
                        to_integer(p->value));
                    add 0, 1 => (to_integer(old(p->value)) + 1 + at(function.entry,
                        (to_integer(count(remaining(p))) - 1))) < (0 + at(function.entry, 3));
                    add 4, 3 => (to_integer(old(p->value)) + 1 + at(function.entry,
                        (to_integer(count(remaining(p))) - 1)) + at(function.entry, (3 -
                        to_integer(count(remaining(p)))))) < (0 + at(function.entry, 3) +
                        at(function.entry, to_integer(p->value)));
                    conclusion 5;
                }
            }
            have (to_integer(old(p->value)) + 1) <= 4294967295 by {
                arithmetic_certificate {
                    negated_goal => 4294967295 < (to_integer(old(p->value)) + 1);
                    premise 0: at(function.entry, (to_integer(count(remaining(p))) - 1)) >=
                        at(function.entry, 1) => at(function.entry, (to_integer(count(remaining(p)))
                        - 1)) >= at(function.entry, 1);
                    premise 1: at(function.entry, to_integer(p->value)) == at(function.entry, (3 -
                        to_integer(count(remaining(p))))) => at(function.entry,
                        to_integer(p->value)) == at(function.entry, (3 -
                        to_integer(count(remaining(p)))));
                    less_equal_from_equal 2 => at(function.entry, to_integer(p->value)) <=
                        at(function.entry, (3 - to_integer(count(remaining(p)))));
                    add 0, 1 => (4294967295 + at(function.entry, 1)) < (to_integer(old(p->value)) +
                        1 + at(function.entry, (to_integer(count(remaining(p))) - 1)));
                    add 4, 3 => (4294967295 + at(function.entry, 1) + at(function.entry,
                        to_integer(p->value))) < (to_integer(old(p->value)) + 1 + at(function.entry,
                        (to_integer(count(remaining(p))) - 1)) + at(function.entry, (3 -
                        to_integer(count(remaining(p))))));
                    conclusion 5;
                }
            }
            have to_integer(p->value) == (to_integer(old(p->value)) + 1) by {
                arithmetic_certificate rules {
                    premise 0: 0 <= (to_integer(old(p->value)) + 1) => 0 <=
                        (to_integer(old(p->value)) + 1);
                    premise 1: (to_integer(old(p->value)) + 1) <= 4294967295 =>
                        (to_integer(old(p->value)) + 1) <= 4294967295;
                    integer_operation_identity bounds [0, 1] => to_integer(p->value) ==
                        (to_integer(old(p->value)) + 1);
                    conclusion 0;
                }
            }
            have -2147483648 <= (to_integer(old(count(remaining(p)))) - 1) by {
                arithmetic_certificate {
                    negated_goal => (to_integer(old(count(remaining(p)))) - 1) < -2147483648;
                    premise 0: at(function.entry, (to_integer(count(remaining(p))) - 1)) >=
                        at(function.entry, 1) => at(function.entry, (to_integer(count(remaining(p)))
                        - 1)) >= at(function.entry, 1);
                    add 0, 1 => ((to_integer(old(count(remaining(p)))) - 1) + at(function.entry, 1))
                        < (-2147483648 + at(function.entry, (to_integer(count(remaining(p))) - 1)));
                    conclusion 2;
                }
            }
            have (to_integer(old(count(remaining(p)))) - 1) <= 2147483647 by {
                arithmetic_certificate {
                    negated_goal => 2147483647 < (to_integer(old(count(remaining(p)))) - 1);
                    premise 0: at(function.entry, (to_integer(count(remaining(p))) - 1)) <=
                        at(function.entry, 3) => at(function.entry, (to_integer(count(remaining(p)))
                        - 1)) <= at(function.entry, 3);
                    add 0, 1 => (2147483647 + at(function.entry, (to_integer(count(remaining(p))) -
                        1))) < ((to_integer(old(count(remaining(p)))) - 1) + at(function.entry, 3));
                    conclusion 2;
                }
            }
            have to_integer(count(remaining(p))) == (to_integer(old(count(remaining(p)))) - 1) by {
                arithmetic_certificate rules {
                    premise 0: -2147483648 <= (to_integer(old(count(remaining(p)))) - 1) =>
                        -2147483648 <= (to_integer(old(count(remaining(p)))) - 1);
                    premise 1: (to_integer(old(count(remaining(p)))) - 1) <= 2147483647 =>
                        (to_integer(old(count(remaining(p)))) - 1) <= 2147483647;
                    integer_operation_identity bounds [0, 1] => to_integer(count(remaining(p))) ==
                        (to_integer(old(count(remaining(p)))) - 1);
                    conclusion 0;
                }
            }
            have to_integer(p->value) <= (3 - to_integer(count(remaining(p)))) by {
                arithmetic_certificate {
                    negated_goal => (3 - to_integer(count(remaining(p)))) < to_integer(p->value);
                    premise 0: at(function.entry, to_integer(p->value)) == at(function.entry, (3 -
                        to_integer(count(remaining(p))))) => at(function.entry,
                        to_integer(p->value)) == at(function.entry, (3 -
                        to_integer(count(remaining(p)))));
                    less_equal_from_equal 1 => at(function.entry, to_integer(p->value)) <=
                        at(function.entry, (3 - to_integer(count(remaining(p)))));
                    premise 1: to_integer(count(remaining(p))) ==
                        (to_integer(old(count(remaining(p)))) - 1) =>
                        to_integer(count(remaining(p))) == (to_integer(old(count(remaining(p)))) -
                        1);
                    less_equal_from_equal 3 => to_integer(count(remaining(p))) <=
                        (to_integer(old(count(remaining(p)))) - 1);
                    premise 2: to_integer(p->value) == (to_integer(old(p->value)) + 1) =>
                        to_integer(p->value) == (to_integer(old(p->value)) + 1);
                    less_equal_from_equal 5 => to_integer(p->value) <= (to_integer(old(p->value)) +
                        1);
                    add 0, 2 => ((3 - to_integer(count(remaining(p)))) + at(function.entry,
                        to_integer(p->value))) < (to_integer(p->value) + at(function.entry, (3 -
                        to_integer(count(remaining(p))))));
                    add 7, 4 => ((3 - to_integer(count(remaining(p)))) + at(function.entry,
                        to_integer(p->value)) + to_integer(count(remaining(p)))) <
                        (to_integer(p->value) + at(function.entry, (3 -
                        to_integer(count(remaining(p))))) + (to_integer(old(count(remaining(p)))) -
                        1));
                    add 8, 6 => ((3 - to_integer(count(remaining(p)))) + at(function.entry,
                        to_integer(p->value)) + to_integer(count(remaining(p))) +
                        to_integer(p->value)) < (to_integer(p->value) + at(function.entry, (3 -
                        to_integer(count(remaining(p))))) + (to_integer(old(count(remaining(p)))) -
                        1) + (to_integer(old(p->value)) + 1));
                    conclusion 9;
                }
            }
            have (3 - to_integer(count(remaining(p)))) <= to_integer(p->value) by {
                arithmetic_certificate {
                    negated_goal => to_integer(p->value) < (3 - to_integer(count(remaining(p))));
                    premise 0: at(function.entry, to_integer(p->value)) == at(function.entry, (3 -
                        to_integer(count(remaining(p))))) => at(function.entry,
                        to_integer(p->value)) == at(function.entry, (3 -
                        to_integer(count(remaining(p)))));
                    less_equal_from_equal 1 reverse => at(function.entry, (3 -
                        to_integer(count(remaining(p))))) <= at(function.entry,
                        to_integer(p->value));
                    premise 1: to_integer(count(remaining(p))) ==
                        (to_integer(old(count(remaining(p)))) - 1) =>
                        to_integer(count(remaining(p))) == (to_integer(old(count(remaining(p)))) -
                        1);
                    less_equal_from_equal 3 reverse => (to_integer(old(count(remaining(p)))) - 1) <=
                        to_integer(count(remaining(p)));
                    premise 2: to_integer(p->value) == (to_integer(old(p->value)) + 1) =>
                        to_integer(p->value) == (to_integer(old(p->value)) + 1);
                    less_equal_from_equal 5 reverse => (to_integer(old(p->value)) + 1) <=
                        to_integer(p->value);
                    add 0, 2 => (to_integer(p->value) + at(function.entry, (3 -
                        to_integer(count(remaining(p)))))) < ((3 - to_integer(count(remaining(p))))
                        + at(function.entry, to_integer(p->value)));
                    add 7, 4 => (to_integer(p->value) + at(function.entry, (3 -
                        to_integer(count(remaining(p))))) + (to_integer(old(count(remaining(p)))) -
                        1)) < ((3 - to_integer(count(remaining(p)))) + at(function.entry,
                        to_integer(p->value)) + to_integer(count(remaining(p))));
                    add 8, 6 => (to_integer(p->value) + at(function.entry, (3 -
                        to_integer(count(remaining(p))))) + (to_integer(old(count(remaining(p)))) -
                        1) + (to_integer(old(p->value)) + 1)) < ((3 -
                        to_integer(count(remaining(p)))) + at(function.entry, to_integer(p->value))
                        + to_integer(count(remaining(p))) + to_integer(p->value));
                    conclusion 9;
                }
            }
            arithmetic_certificate {
                premise 0: to_integer(p->value) <= (3 - to_integer(count(remaining(p)))) =>
                    to_integer(p->value) <= (3 - to_integer(count(remaining(p))));
                premise 1: (3 - to_integer(count(remaining(p)))) <= to_integer(p->value) => (3 -
                    to_integer(count(remaining(p)))) <= to_integer(p->value);
                equal_from_bounds 0, 1 => to_integer(p->value) == (3 -
                    to_integer(count(remaining(p))));
                conclusion 2;
            }
        }
    }
    if report != 0 {
        open(control(p)) {
            step();
            step();
        }
        assumption();
        have to_integer(count(remaining(p))) == (to_integer(old(count(remaining(p)))) - 1) by {
            have -2147483648 <= (to_integer(old(count(remaining(p)))) - 1) by {
                arithmetic_certificate {
                    negated_goal => (to_integer(old(count(remaining(p)))) - 1) < -2147483648;
                    premise 0: at(function.entry, (to_integer(count(remaining(p))) - 1)) >=
                        at(function.entry, 1) => at(function.entry, (to_integer(count(remaining(p)))
                        - 1)) >= at(function.entry, 1);
                    add 0, 1 => ((to_integer(old(count(remaining(p)))) - 1) + at(function.entry, 1))
                        < (-2147483648 + at(function.entry, (to_integer(count(remaining(p))) - 1)));
                    conclusion 2;
                }
            }
            have (to_integer(old(count(remaining(p)))) - 1) <= 2147483647 by {
                arithmetic_certificate {
                    negated_goal => 2147483647 < (to_integer(old(count(remaining(p)))) - 1);
                    premise 0: at(function.entry, (to_integer(count(remaining(p))) - 1)) <=
                        at(function.entry, 3) => at(function.entry, (to_integer(count(remaining(p)))
                        - 1)) <= at(function.entry, 3);
                    add 0, 1 => (2147483647 + at(function.entry, (to_integer(count(remaining(p))) -
                        1))) < ((to_integer(old(count(remaining(p)))) - 1) + at(function.entry, 3));
                    conclusion 2;
                }
            }
            have to_integer(count(remaining(p))) == (to_integer(old(count(remaining(p)))) - 1) by {
                arithmetic_certificate rules {
                    premise 0: -2147483648 <= (to_integer(old(count(remaining(p)))) - 1) =>
                        -2147483648 <= (to_integer(old(count(remaining(p)))) - 1);
                    premise 1: (to_integer(old(count(remaining(p)))) - 1) <= 2147483647 =>
                        (to_integer(old(count(remaining(p)))) - 1) <= 2147483647;
                    integer_operation_identity bounds [0, 1] => to_integer(count(remaining(p))) ==
                        (to_integer(old(count(remaining(p)))) - 1);
                    conclusion 0;
                }
            }
            assumption();
        }
        have to_integer(p->value) == (to_integer(old(p->value)) + 1) by {
            rewrite(at(function.entry, to_integer(p->value)) == at(function.entry, (3 - to_integer(count(remaining(p))))));
            rewrite(to_integer(p->value) == (3 - to_integer(count(remaining(p)))));
            rewrite(to_integer(count(remaining(p))) == (to_integer(old(count(remaining(p)))) - 1));
            normalize();
        }
        assumption();
        assumption();
    } else {
        step();
        step();
        step();
        assumption();
        have to_integer(count(remaining(p))) == (to_integer(old(count(remaining(p)))) - 1) by {
            have -2147483648 <= (to_integer(old(count(remaining(p)))) - 1) by {
                arithmetic_certificate {
                    negated_goal => (to_integer(old(count(remaining(p)))) - 1) < -2147483648;
                    premise 0: at(function.entry, (to_integer(count(remaining(p))) - 1)) >=
                        at(function.entry, 1) => at(function.entry, (to_integer(count(remaining(p)))
                        - 1)) >= at(function.entry, 1);
                    add 0, 1 => ((to_integer(old(count(remaining(p)))) - 1) + at(function.entry, 1))
                        < (-2147483648 + at(function.entry, (to_integer(count(remaining(p))) - 1)));
                    conclusion 2;
                }
            }
            have (to_integer(old(count(remaining(p)))) - 1) <= 2147483647 by {
                arithmetic_certificate {
                    negated_goal => 2147483647 < (to_integer(old(count(remaining(p)))) - 1);
                    premise 0: at(function.entry, (to_integer(count(remaining(p))) - 1)) <=
                        at(function.entry, 3) => at(function.entry, (to_integer(count(remaining(p)))
                        - 1)) <= at(function.entry, 3);
                    add 0, 1 => (2147483647 + at(function.entry, (to_integer(count(remaining(p))) -
                        1))) < ((to_integer(old(count(remaining(p)))) - 1) + at(function.entry, 3));
                    conclusion 2;
                }
            }
            have to_integer(count(remaining(p))) == (to_integer(old(count(remaining(p)))) - 1) by {
                arithmetic_certificate rules {
                    premise 0: -2147483648 <= (to_integer(old(count(remaining(p)))) - 1) =>
                        -2147483648 <= (to_integer(old(count(remaining(p)))) - 1);
                    premise 1: (to_integer(old(count(remaining(p)))) - 1) <= 2147483647 =>
                        (to_integer(old(count(remaining(p)))) - 1) <= 2147483647;
                    integer_operation_identity bounds [0, 1] => to_integer(count(remaining(p))) ==
                        (to_integer(old(count(remaining(p)))) - 1);
                    conclusion 0;
                }
            }
            assumption();
        }
        have to_integer(p->value) == (to_integer(old(p->value)) + 1) by {
            rewrite(at(function.entry, to_integer(p->value)) == at(function.entry, (3 - to_integer(count(remaining(p))))));
            rewrite(to_integer(p->value) == (3 - to_integer(count(remaining(p)))));
            rewrite(to_integer(count(remaining(p))) == (to_integer(old(count(remaining(p)))) - 1));
            normalize();
        }
        assumption();
        assumption();
    }
}
uint32 sequential_early(struct counter* p) {
    consumes storage(p);
    produces p->value;
    ensures result == 2;
} by {
    unfold(storage(p));
    step();
    fold(3 of remaining(p));
    have to_integer(p->value) == (3 - to_integer(count(remaining(p)))) by {
        have -2147483648 <= (to_integer(old(count(remaining(p)))) + 3) by {
            arithmetic_certificate {
                negated_goal => (to_integer(old(count(remaining(p)))) + 3) < -2147483648;
                premise 0: 0 <= to_integer(old(count(remaining(p)))) => 0 <=
                    to_integer(old(count(remaining(p))));
                add 0, 1 => (to_integer(old(count(remaining(p)))) + 3 + 0) < (-2147483648 +
                    to_integer(old(count(remaining(p)))));
                conclusion 2;
            }
        }
        have (to_integer(old(count(remaining(p)))) + 3) <= 2147483647 by {
            arithmetic_certificate {
                negated_goal => 2147483647 < (to_integer(old(count(remaining(p)))) + 3);
                premise 0: to_integer(old(count(remaining(p)))) == 0 =>
                    to_integer(old(count(remaining(p)))) == 0;
                less_equal_from_equal 1 => to_integer(old(count(remaining(p)))) <= 0;
                add 0, 2 => (2147483647 + to_integer(old(count(remaining(p))))) <
                    (to_integer(old(count(remaining(p)))) + 3 + 0);
                conclusion 3;
            }
        }
        have to_integer(count(remaining(p))) == (to_integer(old(count(remaining(p)))) + 3) by {
            arithmetic_certificate rules {
                premise 0: -2147483648 <= (to_integer(old(count(remaining(p)))) + 3) => -2147483648
                    <= (to_integer(old(count(remaining(p)))) + 3);
                premise 1: (to_integer(old(count(remaining(p)))) + 3) <= 2147483647 =>
                    (to_integer(old(count(remaining(p)))) + 3) <= 2147483647;
                integer_operation_identity bounds [0, 1] => to_integer(count(remaining(p))) ==
                    (to_integer(old(count(remaining(p)))) + 3);
                conclusion 0;
            }
        }
        have to_integer(p->value) <= (3 - to_integer(count(remaining(p)))) by {
            arithmetic_certificate {
                negated_goal => (3 - to_integer(count(remaining(p)))) < to_integer(p->value);
                premise 0: to_integer(count(remaining(p))) == (to_integer(old(count(remaining(p))))
                    + 3) => to_integer(count(remaining(p))) == (to_integer(old(count(remaining(p))))
                    + 3);
                less_equal_from_equal 1 => to_integer(count(remaining(p))) <=
                    (to_integer(old(count(remaining(p)))) + 3);
                premise 1: to_integer(old(count(remaining(p)))) == 0 =>
                    to_integer(old(count(remaining(p)))) == 0;
                less_equal_from_equal 3 => to_integer(old(count(remaining(p)))) <= 0;
                add 0, 2 => ((3 - to_integer(count(remaining(p)))) +
                    to_integer(count(remaining(p)))) < (to_integer(p->value) +
                    (to_integer(old(count(remaining(p)))) + 3));
                add 5, 4 => ((3 - to_integer(count(remaining(p)))) + to_integer(count(remaining(p)))
                    + to_integer(old(count(remaining(p))))) < (to_integer(p->value) +
                    (to_integer(old(count(remaining(p)))) + 3) + 0);
                conclusion 6;
            }
        }
        have (3 - to_integer(count(remaining(p)))) <= to_integer(p->value) by {
            arithmetic_certificate {
                negated_goal => to_integer(p->value) < (3 - to_integer(count(remaining(p))));
                premise 0: to_integer(count(remaining(p))) == (to_integer(old(count(remaining(p))))
                    + 3) => to_integer(count(remaining(p))) == (to_integer(old(count(remaining(p))))
                    + 3);
                less_equal_from_equal 1 reverse => (to_integer(old(count(remaining(p)))) + 3) <=
                    to_integer(count(remaining(p)));
                premise 1: 0 <= to_integer(old(count(remaining(p)))) => 0 <=
                    to_integer(old(count(remaining(p))));
                add 0, 2 => (to_integer(p->value) + (to_integer(old(count(remaining(p)))) + 3)) <
                    ((3 - to_integer(count(remaining(p)))) + to_integer(count(remaining(p))));
                add 4, 3 => (to_integer(p->value) + (to_integer(old(count(remaining(p)))) + 3) + 0)
                    < ((3 - to_integer(count(remaining(p)))) + to_integer(count(remaining(p))) +
                    to_integer(old(count(remaining(p)))));
                conclusion 5;
            }
        }
        arithmetic_certificate {
            premise 0: to_integer(p->value) <= (3 - to_integer(count(remaining(p)))) =>
                to_integer(p->value) <= (3 - to_integer(count(remaining(p))));
            premise 1: (3 - to_integer(count(remaining(p)))) <= to_integer(p->value) => (3 -
                to_integer(count(remaining(p)))) <= to_integer(p->value);
            equal_from_bounds 0, 1 => to_integer(p->value) == (3 - to_integer(count(remaining(p))));
            conclusion 2;
        }
    }
    fold(control(p));
    step() by {
        arithmetic_certificate signed_int32 {
            premise 0: old((count(remaining(p)) as int32)) >= at(function.entry, 0) =>
                old((count(remaining(p)) as int32)) >= at(function.entry, 0);
            premise 1: at(function.entry, to_integer(count(remaining(p)))) == at(function.entry, 0)
                => at(function.entry, to_integer(count(remaining(p)))) == at(function.entry, 0);
            less_equal_from_equal 1 => at(function.entry, to_integer(count(remaining(p)))) <=
                at(function.entry, 0);
            interval_from_affine 0 (at(function.entry, to_integer(count(remaining(p))))) (0)
                (2147483647);
            interval_from_affine 2 (at(function.entry, to_integer(count(remaining(p)))))
                (-2147483648) (0);
            interval_intersect 3, 4 (0) (0);
            interval_atom (3) (3) (3);
            interval_add_bounded 5, 6 (3) (3);
            trivial => -1 <= 0;
            add 0, 8 => ((at(function.entry, 0) + -1) as int32) <= ((old(count(remaining(p))) +
                0) as int32);
            affine_conclusion 9 7 => (count(remaining(p)) as int32) > (1 as int32);
            conclusion 10;
        }
    }
    step() by {
        arithmetic_certificate signed_int32 {
            premise 0: old((count(remaining(p)) as int32)) >= at(function.entry, 0) =>
                old((count(remaining(p)) as int32)) >= at(function.entry, 0);
            premise 1: at(function.entry, to_integer(count(remaining(p)))) == at(function.entry, 0)
                => at(function.entry, to_integer(count(remaining(p)))) == at(function.entry, 0);
            less_equal_from_equal 1 => at(function.entry, to_integer(count(remaining(p)))) <=
                at(function.entry, 0);
            interval_from_affine 0 (at(function.entry, to_integer(count(remaining(p))))) (0)
                (2147483647);
            interval_from_affine 2 (at(function.entry, to_integer(count(remaining(p)))))
                (-2147483648) (0);
            interval_intersect 3, 4 (0) (0);
            interval_atom (2) (2) (2);
            interval_add_bounded 5, 6 (2) (2);
            affine_conclusion 0 7 => (count(remaining(p)) as int32) > (1 as int32);
            conclusion 8;
        }
    }
    unfold(control(p));
    unfold(remaining(p));
    unfold(authority(remaining(p)));
    step();
    assumption();
    have result == 2 by {
        assumption();
    }
    assumption();
}
```

```expect
pass
```
