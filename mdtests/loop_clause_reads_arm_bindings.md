# A loop written inside a proof `match` arm names the arm's bindings

A proof `match` on an instance's model binds the constructor's payloads for
the arm, and every term the arm writes may name them: `have` goals, theorem
arguments, and, when the arm contains a loop, that loop's clauses. Here the
loop's invariant states the binder's model as the constructor built from the
arm's pointer, integer, and model bindings, and the post-loop claim follows
from it. Loop clauses are lowered when the loop tactic runs at its frontier,
so the frontier's proof locals are resolved into them first, exactly as a
`have` goal at that point resolves the same names.

```c filename=loop_clause_reads_arm_bindings.c
struct node { int value; struct node *left; };

int spin(struct node *p, int n) {
    int i;
    i = 0;
    while (i < n) {
        i = i + 1;
    }
    return p->value;
}
```

```click
verifying "loop_clause_reads_arm_bindings.c";

spec enum Tree {
    Empty,
    Node(struct node*, int, Tree),
}

resource tree_at(p: struct node*) {
    field model: Tree;
    match model {
        Tree::Empty => { fact p == 0; },
        Tree::Node(id, value, left_model) => {
            owns p->value;
            owns p->left;
            owns left: tree_at(p->left);
            fact p != 0;
            fact p == id;
            fact p->value == value;
            fact left.model == left_model;
        },
    }
}

int spin(struct node* p, int n) {
    requires n >= 0;
    owns t: tree_at(p);
    requires t.model != Tree::Empty;
    ensures t.model == old(t.model);
} by {
    match t.model {
        Tree::Empty => { contradiction(t.model == Tree::Empty); },
        Tree::Node(id, value, left_model) => {
            step();
            step();
            loop {
                decreases n - i;
                owns t: tree_at(p);
                invariant i >= 0;
                invariant i <= n;
                invariant t.model == Tree::Node(id, value, left_model);

                initialize by solve();
                preserve by {
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
                                    intro();
                                    intro();
                                    assumption();
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
                                                negated_goal => 2147483647 < (to_integer(at(region(3).entry, i)) + 1);
                                                premise 0: at(region(3).entry, i) < at(region(3).entry, n) =>
                                                    at(region(3).entry, i) < at(region(3).entry, n);
                                                type_range => to_integer(n) <= 2147483647;
                                                add 0, 1 => (2147483647 + 1 + (at(region(3).entry, to_integer(i)) + 1))
                                                    <= (to_integer(at(region(3).entry, i)) + 1 + at(region(3).entry,
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
                                            less_equal_from_equal 1 => to_integer(i) <= (to_integer(at(region(3).entry,
                                                i)) + 1);
                                            add 0, 2 => (at(region(3).entry, to_integer(i)) + to_integer(i)) <
                                                (at(region(3).entry, to_integer(n)) + (to_integer(at(region(3).entry,
                                                i)) + 1));
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
                                                negated_goal => 2147483647 < (to_integer(at(region(3).entry, i)) + 1);
                                                premise 0: at(region(3).entry, i) < at(region(3).entry, n) =>
                                                    at(region(3).entry, i) < at(region(3).entry, n);
                                                type_range => to_integer(n) <= 2147483647;
                                                add 0, 1 => (2147483647 + 1 + (at(region(3).entry, to_integer(i)) + 1))
                                                    <= (to_integer(at(region(3).entry, i)) + 1 + at(region(3).entry,
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
                                            less_equal_from_equal 0 reverse => (to_integer(at(region(3).entry, i)) + 1)
                                                <= to_integer(i);
                                            conclusion 1;
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
            step();
            solve();
        },
    }
}
```

```expect
pass
```
