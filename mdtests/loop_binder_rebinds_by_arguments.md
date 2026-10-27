# A loop binder is rebound by its arguments, not by the body's name

The body folds its result under a new name, `d`. The back edge selects the
loop binder the same way the head did — the one owned `counter(p)` — so `c`
names the instance the body called `d`, and the invariants are checked against
that instance's fresh model. No binder map is written anywhere.

The head's model `c.count` is an arbitrary value of its own, so before touching
the cell the body states what the invariants make it: `c.count == i`. Nothing
else bounds the cell that the increment writes.

```c filename=loop_binder_rebinds_by_arguments.c
struct cell { int32 value; };

void bump_n(struct cell* p, int32 n) {
    int32 i;
    i = 0;
    while (i < n) {
        p->value = p->value + 1;
        i = i + 1;
    }
}
```

```click
verifying "loop_binder_rebinds_by_arguments.c";

resource counter(p: struct cell*) {
    field count: int32;
    owns p->value;
    fact p->value == count;
}

void bump_n(struct cell* p, int32 n) {
    requires n >= 0;
    requires n <= 1000;
    owns c: counter(p);
    requires c.count == 0;
    ensures to_integer(c.count) == to_integer(old(c.count) + n);
} by {
    step();
    step();
    loop {
        decreases n - i;
        owns c: counter(p);
        invariant i >= 0;
        invariant i <= n;
        invariant to_integer(c.count) == to_integer(old(c.count) + i);

        initialize by solve();
        preserve by {
            have c.count == i by {
                rewrite(to_integer(c.count) == to_integer((old(c.count) + i)));
                rewrite(old(c.count) == 0);
                normalize();
            }
            unfold(c);
            step();
            step();
            let d = fold(counter(p), { count: (old(c.count) + i) });
            close_invariants() by {
                both {
                    arithmetic_certificate signed_int32 {
                        premise 0: at(region(3).entry, i) >= at(region(3).entry, 0) => at(region(3).entry, i) >=
                            at(region(3).entry, 0);
                        premise 1: at(region(3).entry, i) < at(region(3).entry, n) => at(region(3).entry, i) <
                            at(region(3).entry, n);
                        int32_range => n <= 2147483647;
                        add 1, 2 => ((at(region(3).entry, i) + n) as int32) < ((at(region(3).entry, n) +
                            2147483647) as int32);
                        interval_from_affine 0 (at(region(3).entry, i)) (0) (2147483647);
                        interval_from_affine 3 (at(region(3).entry, i)) (-2147483648) (2147483646);
                        interval_intersect 4, 5 (0) (2147483646);
                        interval_atom (1) (1) (1);
                        interval_add_bounded 6, 7 (1) (2147483647);
                        trivial => -1 <= 0;
                        add 0, 9 => ((at(region(3).entry, 0) + -1) as int32) <= ((at(region(3).entry, i) + 0) as
                            int32);
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
                            add 0, 1 => ((at(region(3).entry, i) + n) as int32) < ((at(region(3).entry, n) +
                                2147483647) as int32);
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
                                        premise 0: at(region(3).entry, i) < at(region(3).entry, n) =>
                                            at(region(3).entry, i) < at(region(3).entry, n);
                                        premise 1: n <= 1000 => n <= 1000;
                                        add 0, 1 => (at(region(3).entry, to_integer(i)) + to_integer(n)) <
                                            (at(region(3).entry, to_integer(n)) + 1000);
                                        trivial => -2147482647 <= 0;
                                        add 2, 3 => (at(region(3).entry, to_integer(i)) + to_integer(n) +
                                            -2147482647) < (at(region(3).entry, to_integer(n)) + 1000 + 0);
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
                                        premise 0: n <= 1000 => n <= 1000;
                                        premise 1: at(region(3).entry, i) < at(region(3).entry, n) =>
                                            at(region(3).entry, i) < at(region(3).entry, n);
                                        add 0, 1 => (to_integer(n) + at(region(3).entry, to_integer(i))) < (1000
                                            + at(region(3).entry, to_integer(n)));
                                        trivial => -2147482647 <= 0;
                                        add 2, 3 => (to_integer(n) + at(region(3).entry, to_integer(i)) +
                                            -2147482647) < (1000 + at(region(3).entry, to_integer(n)) + 0);
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
    have i == n;
}
```

```expect
pass
```
