# loop invariant lowers old-state stdlib count

This checks that `old(...)` in a loop invariant re-elaborates its body in the
entry-state spec context. In particular, `old(permutation::count(...))` reaches the stdlib
`count` function and keeps its `.fold` as pure spec/core over entry memory.

```c filename=loop_old_count_invariant.c
int32 loop_old_count_invariant(int32 p[3]) {
    int32 i;
    i = 0;
    while (i < 3) {
        i = i + 1;
    }
    return i;
}
```

```click
import click::permutation;

verifying "loop_old_count_invariant.c";

int32 loop_old_count_invariant(int32 p[3]) {
    requires viewable(p[0..3]);
    ensures result_value: result == 3;
} by {
    step();
    step();
    loop {
        decreases (3 - i);
        invariant i >= 0 and i <= 3;
        invariant old(permutation::count(p, 0, 3, p[0])) == old(permutation::count(p, 0, 3, p[0]));
        initialize by {
            have i >= 0 and i <= 3 by {
                both {
                    normalize();
                } and {
                    normalize();
                }
            }
            have old(permutation::count(p, 0, 3, p[0])) == old(permutation::count(p, 0, 3, p[0])) by {
                normalize();
            }
        }
        preserve by {
            mark iteration;
            step();
            have i >= 0 and i <= 3 by {
                both {
                    extract(at(region(3).entry, i) >= at(region(3).entry, 0));
                    arithmetic_certificate signed_int32 {
                        premise 0: at(region(3).entry, i) >= at(region(3).entry, 0) => at(region(3).entry, i) >=
                            at(region(3).entry, 0);
                        premise 1: at(region(3).entry, i) < at(region(3).entry, 3) => at(region(3).entry, i) <
                            at(region(3).entry, 3);
                        interval_from_affine 0 (at(region(3).entry, i)) (0) (2147483647);
                        interval_from_affine 1 (at(region(3).entry, i)) (-2147483648) (2);
                        interval_intersect 2, 3 (0) (2);
                        interval_atom (1) (1) (1);
                        interval_add_bounded 4, 5 (1) (3);
                        trivial => -1 <= 0;
                        add 0, 7 => ((at(region(3).entry, 0) + -1) as int32) <= ((at(region(3).entry, i) + 0) as
                            int32);
                        affine_conclusion 8 6 => (i as int32) >= (0 as int32);
                        conclusion 9;
                    }
                } and {
                    arithmetic_certificate signed_int32 {
                        premise 0: at(region(3).entry, i) < at(region(3).entry, 3) => at(region(3).entry, i) <
                            at(region(3).entry, 3);
                        interval_from_affine 0 (at(region(3).entry, i)) (-2147483648) (2);
                        interval_atom (1) (1) (1);
                        interval_add_bounded 1, 2 (-2147483647) (3);
                        affine_conclusion 0 3 => (i as int32) <= (3 as int32);
                        conclusion 4;
                    }
                }
            }
            close_invariants() by {
                both {
                    normalize();
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
                                premise 0: at(region(3).entry, i) < at(region(3).entry, 3) =>
                                    at(region(3).entry, i) < at(region(3).entry, 3);
                                trivial => -2147483644 <= 0;
                                add 0, 1 => (at(region(3).entry, to_integer(i)) + -2147483644) <
                                    (at(region(3).entry, 3) + 0);
                                conclusion 2;
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
                            premise 0: at(region(3).entry, i) < at(region(3).entry, 3) => at(region(3).entry, i)
                                < at(region(3).entry, 3);
                            premise 1: to_integer(i) == (to_integer(at(region(3).entry, i)) + 1) =>
                                to_integer(i) == (to_integer(at(region(3).entry, i)) + 1);
                            less_equal_from_equal 1 => to_integer(i) <= (to_integer(at(region(3).entry, i)) +
                                1);
                            add 0, 2 => (at(region(3).entry, to_integer(i)) + to_integer(i)) <
                                (at(region(3).entry, 3) + (to_integer(at(region(3).entry, i)) + 1));
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
                                premise 0: at(region(3).entry, i) < at(region(3).entry, 3) =>
                                    at(region(3).entry, i) < at(region(3).entry, 3);
                                trivial => -2147483644 <= 0;
                                add 0, 1 => (at(region(3).entry, to_integer(i)) + -2147483644) <
                                    (at(region(3).entry, 3) + 0);
                                conclusion 2;
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
    step();
    have result == 3 by {
        solve() using {
            at(loop(0).exit, i) <= at(loop(0).exit, 3);
            not at(loop(0).exit, i) < at(loop(0).exit, 3);
        };
    }
    assumption();
}
```

```expect
pass
```
