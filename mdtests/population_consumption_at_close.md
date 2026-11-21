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
    with(control(p)) {
        have to_integer(count(remaining(p))) <= 3 by {
            known();
        }
    }
    with(control(p)) {
        have (to_integer(count(remaining(p))) - 1) >= 1 by {
            solve() using { to_integer(count(remaining(p))) > 1; };
        }
        have (to_integer(count(remaining(p))) - 1) <= 3 by {
            solve() using { to_integer(count(remaining(p))) <= 3; };
        }
        unfold(remaining(p));
        step();
        have to_integer(p->value) == (3 - to_integer(count(remaining(p)))) by {
            have 0 <= (to_integer(old(p->value)) + 1) by {
                solve() using { at(function.entry, (to_integer(count(remaining(p))) - 1)) <=
                        at(function.entry, 3); at(function.entry, to_integer(p->value)) == at(function.entry, (3 -
                        to_integer(count(remaining(p))))); };
            }
            have (to_integer(old(p->value)) + 1) <= 4294967295 by {
                solve() using { at(function.entry, (to_integer(count(remaining(p))) - 1)) >=
                        at(function.entry, 1); at(function.entry, to_integer(p->value)) == at(function.entry, (3 -
                        to_integer(count(remaining(p))))); };
            }
            have to_integer(p->value) == (to_integer(old(p->value)) + 1) by {
                solve() using { 0 <= (to_integer(old(p->value)) + 1); (to_integer(old(p->value)) + 1) <= 4294967295; };
            }
            have -2147483648 <= (to_integer(old(count(remaining(p)))) - 1) by {
                solve() using { at(function.entry, (to_integer(count(remaining(p))) - 1)) >=
                        at(function.entry, 1); };
            }
            have (to_integer(old(count(remaining(p)))) - 1) <= 2147483647 by {
                solve() using { at(function.entry, (to_integer(count(remaining(p))) - 1)) <=
                        at(function.entry, 3); };
            }
            have to_integer(count(remaining(p))) == (to_integer(old(count(remaining(p)))) - 1) by {
                solve() using { -2147483648 <= (to_integer(old(count(remaining(p)))) - 1); (to_integer(old(count(remaining(p)))) - 1) <= 2147483647; };
            }
            have to_integer(p->value) <= (3 - to_integer(count(remaining(p)))) by {
                solve() using { at(function.entry, to_integer(p->value)) == at(function.entry, (3 -
                        to_integer(count(remaining(p))))); to_integer(count(remaining(p))) ==
                        (to_integer(old(count(remaining(p)))) - 1); to_integer(p->value) == (to_integer(old(p->value)) + 1); };
            }
            have (3 - to_integer(count(remaining(p)))) <= to_integer(p->value) by {
                solve() using { at(function.entry, to_integer(p->value)) == at(function.entry, (3 -
                        to_integer(count(remaining(p))))); to_integer(count(remaining(p))) ==
                        (to_integer(old(count(remaining(p)))) - 1); to_integer(p->value) == (to_integer(old(p->value)) + 1); };
            }
            solve() using { to_integer(p->value) <= (3 - to_integer(count(remaining(p)))); (3 - to_integer(count(remaining(p)))) <= to_integer(p->value); };
        }
    }
    with(control(p)) {
        step();
    }
    known();
    have to_integer(count(remaining(p))) == (to_integer(old(count(remaining(p)))) - 1) by {
        have -2147483648 <= (to_integer(old(count(remaining(p)))) - 1) by {
            solve() using { at(function.entry, (to_integer(count(remaining(p))) - 1)) >=
                    at(function.entry, 1); };
        }
        have (to_integer(old(count(remaining(p)))) - 1) <= 2147483647 by {
            solve() using { at(function.entry, (to_integer(count(remaining(p))) - 1)) <=
                    at(function.entry, 3); };
        }
        have to_integer(count(remaining(p))) == (to_integer(old(count(remaining(p)))) - 1) by {
            solve() using { -2147483648 <= (to_integer(old(count(remaining(p)))) - 1); (to_integer(old(count(remaining(p)))) - 1) <= 2147483647; };
        }
        known();
    }
    have to_integer(p->value) == (to_integer(old(p->value)) + 1) by {
        rewrite(at(function.entry, to_integer(p->value)), at(function.entry, (3 - to_integer(count(remaining(p))))));
        rewrite(to_integer(p->value), (3 - to_integer(count(remaining(p)))));
        rewrite(to_integer(count(remaining(p))), (to_integer(old(count(remaining(p)))) - 1));
        normalize();
    }
    known();
    known();
}
uint32 read_current(struct counter* p) {
    owns control(p);
} by {
    with(control(p)) {
        step();
    }
    known();
}
uint32 contribute_nested(struct counter* p) {
    owns control(p);
    consumes remaining(p);
    requires count(remaining(p)) > 1;
    ensures count(remaining(p)) == old(count(remaining(p))) - 1;
    ensures p->value == old(p->value) + 1;
} by {
    with(control(p)) {
        have (to_integer(count(remaining(p))) - 1) >= 1 by {
            solve() using { to_integer(count(remaining(p))) > 1; };
        }
        have (to_integer(count(remaining(p))) - 1) <= 3 by {
            solve() using { to_integer(count(remaining(p))) <= 3; };
        }
        unfold(remaining(p));
        step();
        have to_integer(p->value) == (3 - to_integer(count(remaining(p)))) by {
            have 0 <= (to_integer(old(p->value)) + 1) by {
                solve() using { at(function.entry, (to_integer(count(remaining(p))) - 1)) <=
                        at(function.entry, 3); at(function.entry, to_integer(p->value)) == at(function.entry, (3 -
                        to_integer(count(remaining(p))))); };
            }
            have (to_integer(old(p->value)) + 1) <= 4294967295 by {
                solve() using { at(function.entry, (to_integer(count(remaining(p))) - 1)) >=
                        at(function.entry, 1); at(function.entry, to_integer(p->value)) == at(function.entry, (3 -
                        to_integer(count(remaining(p))))); };
            }
            have to_integer(p->value) == (to_integer(old(p->value)) + 1) by {
                solve() using { 0 <= (to_integer(old(p->value)) + 1); (to_integer(old(p->value)) + 1) <= 4294967295; };
            }
            have -2147483648 <= (to_integer(old(count(remaining(p)))) - 1) by {
                solve() using { at(function.entry, (to_integer(count(remaining(p))) - 1)) >=
                        at(function.entry, 1); };
            }
            have (to_integer(old(count(remaining(p)))) - 1) <= 2147483647 by {
                solve() using { at(function.entry, (to_integer(count(remaining(p))) - 1)) <=
                        at(function.entry, 3); };
            }
            have to_integer(count(remaining(p))) == (to_integer(old(count(remaining(p)))) - 1) by {
                solve() using { -2147483648 <= (to_integer(old(count(remaining(p)))) - 1); (to_integer(old(count(remaining(p)))) - 1) <= 2147483647; };
            }
            have to_integer(p->value) <= (3 - to_integer(count(remaining(p)))) by {
                solve() using { at(function.entry, to_integer(p->value)) == at(function.entry, (3 -
                        to_integer(count(remaining(p))))); to_integer(count(remaining(p))) ==
                        (to_integer(old(count(remaining(p)))) - 1); to_integer(p->value) == (to_integer(old(p->value)) + 1); };
            }
            have (3 - to_integer(count(remaining(p)))) <= to_integer(p->value) by {
                solve() using { at(function.entry, to_integer(p->value)) == at(function.entry, (3 -
                        to_integer(count(remaining(p))))); to_integer(count(remaining(p))) ==
                        (to_integer(old(count(remaining(p)))) - 1); to_integer(p->value) == (to_integer(old(p->value)) + 1); };
            }
            solve() using { to_integer(p->value) <= (3 - to_integer(count(remaining(p)))); (3 - to_integer(count(remaining(p)))) <= to_integer(p->value); };
        }
    }
    step();
    with(control(p)) {
        have to_integer(p->value) == (to_integer(old(p->value)) + 1) by {
            have to_integer(p->value) <= (to_integer(old(p->value)) + 1) by {
                have -2147483648 <= (to_integer(old(count(remaining(p)))) - 1) by {
                    solve() using { at(function.entry, (to_integer(count(remaining(p))) - 1)) >=
                            at(function.entry, 1); };
                }
                have (to_integer(old(count(remaining(p)))) - 1) <= 2147483647 by {
                    solve() using { at(function.entry, (to_integer(count(remaining(p))) - 1)) <=
                            at(function.entry, 3); };
                }
                have to_integer(count(remaining(p))) == (to_integer(old(count(remaining(p)))) - 1) by {
                    solve() using { -2147483648 <= (to_integer(old(count(remaining(p)))) - 1); (to_integer(old(count(remaining(p)))) - 1) <= 2147483647; };
                }
                solve() using { at(function.entry, to_integer(p->value)) == at(function.entry, (3 -
                        to_integer(count(remaining(p))))); to_integer(count(remaining(p))) ==
                        (to_integer(old(count(remaining(p)))) - 1); to_integer(p->value) == (3 - to_integer(count(remaining(p)))); };
            }
            have (to_integer(old(p->value)) + 1) <= to_integer(p->value) by {
                have -2147483648 <= (to_integer(old(count(remaining(p)))) - 1) by {
                    solve() using { at(function.entry, (to_integer(count(remaining(p))) - 1)) >=
                            at(function.entry, 1); };
                }
                have (to_integer(old(count(remaining(p)))) - 1) <= 2147483647 by {
                    solve() using { at(function.entry, (to_integer(count(remaining(p))) - 1)) <=
                            at(function.entry, 3); };
                }
                have to_integer(count(remaining(p))) == (to_integer(old(count(remaining(p)))) - 1) by {
                    solve() using { -2147483648 <= (to_integer(old(count(remaining(p)))) - 1); (to_integer(old(count(remaining(p)))) - 1) <= 2147483647; };
                }
                solve() using { at(function.entry, to_integer(p->value)) == at(function.entry, (3 -
                        to_integer(count(remaining(p))))); to_integer(count(remaining(p))) ==
                        (to_integer(old(count(remaining(p)))) - 1); to_integer(p->value) == (3 - to_integer(count(remaining(p)))); };
            }
            solve() using { to_integer(p->value) <= (to_integer(old(p->value)) + 1); (to_integer(old(p->value)) + 1) <= to_integer(p->value); };
        }
    }
    step();
    known();
    have to_integer(count(remaining(p))) == (to_integer(old(count(remaining(p)))) - 1) by {
        have to_integer(count(remaining(p))) <= (to_integer(old(count(remaining(p)))) - 1) by {
            solve() using { at(function.entry, to_integer(p->value)) == at(function.entry, (3 -
                    to_integer(count(remaining(p))))); to_integer(p->value) == (3 - to_integer(count(remaining(p)))); to_integer(p->value) == (to_integer(old(p->value)) + 1); };
        }
        have (to_integer(old(count(remaining(p)))) - 1) <= to_integer(count(remaining(p))) by {
            solve() using { at(function.entry, to_integer(p->value)) == at(function.entry, (3 -
                    to_integer(count(remaining(p))))); to_integer(p->value) == (3 - to_integer(count(remaining(p)))); to_integer(p->value) == (to_integer(old(p->value)) + 1); };
        }
        solve() using { to_integer(count(remaining(p))) <= (to_integer(old(count(remaining(p)))) - 1); (to_integer(old(count(remaining(p)))) - 1) <= to_integer(count(remaining(p))); };
    }
    have to_integer(p->value) == (to_integer(old(p->value)) + 1) by {
        known();
    }
    known();
    known();
}
uint32 contribute_branch(struct counter* p, int32 report) {
    owns control(p);
    consumes remaining(p);
    requires count(remaining(p)) > 1;
    ensures count(remaining(p)) == old(count(remaining(p))) - 1;
    ensures p->value == old(p->value) + 1;
} by {
    with(control(p)) {
        have (to_integer(count(remaining(p))) - 1) >= 1 by {
            solve() using { to_integer(count(remaining(p))) > 1; };
        }
        have (to_integer(count(remaining(p))) - 1) <= 3 by {
            solve() using { to_integer(count(remaining(p))) <= 3; };
        }
        unfold(remaining(p));
        step();
        have to_integer(p->value) == (3 - to_integer(count(remaining(p)))) by {
            have 0 <= (to_integer(old(p->value)) + 1) by {
                solve() using { at(function.entry, (to_integer(count(remaining(p))) - 1)) <=
                        at(function.entry, 3); at(function.entry, to_integer(p->value)) == at(function.entry, (3 -
                        to_integer(count(remaining(p))))); };
            }
            have (to_integer(old(p->value)) + 1) <= 4294967295 by {
                solve() using { at(function.entry, (to_integer(count(remaining(p))) - 1)) >=
                        at(function.entry, 1); at(function.entry, to_integer(p->value)) == at(function.entry, (3 -
                        to_integer(count(remaining(p))))); };
            }
            have to_integer(p->value) == (to_integer(old(p->value)) + 1) by {
                solve() using { 0 <= (to_integer(old(p->value)) + 1); (to_integer(old(p->value)) + 1) <= 4294967295; };
            }
            have -2147483648 <= (to_integer(old(count(remaining(p)))) - 1) by {
                solve() using { at(function.entry, (to_integer(count(remaining(p))) - 1)) >=
                        at(function.entry, 1); };
            }
            have (to_integer(old(count(remaining(p)))) - 1) <= 2147483647 by {
                solve() using { at(function.entry, (to_integer(count(remaining(p))) - 1)) <=
                        at(function.entry, 3); };
            }
            have to_integer(count(remaining(p))) == (to_integer(old(count(remaining(p)))) - 1) by {
                solve() using { -2147483648 <= (to_integer(old(count(remaining(p)))) - 1); (to_integer(old(count(remaining(p)))) - 1) <= 2147483647; };
            }
            have to_integer(p->value) <= (3 - to_integer(count(remaining(p)))) by {
                solve() using { at(function.entry, to_integer(p->value)) == at(function.entry, (3 -
                        to_integer(count(remaining(p))))); to_integer(count(remaining(p))) ==
                        (to_integer(old(count(remaining(p)))) - 1); to_integer(p->value) == (to_integer(old(p->value)) + 1); };
            }
            have (3 - to_integer(count(remaining(p)))) <= to_integer(p->value) by {
                solve() using { at(function.entry, to_integer(p->value)) == at(function.entry, (3 -
                        to_integer(count(remaining(p))))); to_integer(count(remaining(p))) ==
                        (to_integer(old(count(remaining(p)))) - 1); to_integer(p->value) == (to_integer(old(p->value)) + 1); };
            }
            solve() using { to_integer(p->value) <= (3 - to_integer(count(remaining(p)))); (3 - to_integer(count(remaining(p)))) <= to_integer(p->value); };
        }
    }
    if report != 0 {
        with(control(p)) {
            step();
            step();
        }
        known();
        have to_integer(count(remaining(p))) == (to_integer(old(count(remaining(p)))) - 1) by {
            have -2147483648 <= (to_integer(old(count(remaining(p)))) - 1) by {
                solve() using { at(function.entry, (to_integer(count(remaining(p))) - 1)) >=
                        at(function.entry, 1); };
            }
            have (to_integer(old(count(remaining(p)))) - 1) <= 2147483647 by {
                solve() using { at(function.entry, (to_integer(count(remaining(p))) - 1)) <=
                        at(function.entry, 3); };
            }
            have to_integer(count(remaining(p))) == (to_integer(old(count(remaining(p)))) - 1) by {
                solve() using { -2147483648 <= (to_integer(old(count(remaining(p)))) - 1); (to_integer(old(count(remaining(p)))) - 1) <= 2147483647; };
            }
            known();
        }
        have to_integer(p->value) == (to_integer(old(p->value)) + 1) by {
            rewrite(at(function.entry, to_integer(p->value)), at(function.entry, (3 - to_integer(count(remaining(p))))));
            rewrite(to_integer(p->value), (3 - to_integer(count(remaining(p)))));
            rewrite(to_integer(count(remaining(p))), (to_integer(old(count(remaining(p)))) - 1));
            normalize();
        }
        known();
        known();
    } else {
        step();
        step();
        step();
        known();
        have to_integer(count(remaining(p))) == (to_integer(old(count(remaining(p)))) - 1) by {
            have -2147483648 <= (to_integer(old(count(remaining(p)))) - 1) by {
                solve() using { at(function.entry, (to_integer(count(remaining(p))) - 1)) >=
                        at(function.entry, 1); };
            }
            have (to_integer(old(count(remaining(p)))) - 1) <= 2147483647 by {
                solve() using { at(function.entry, (to_integer(count(remaining(p))) - 1)) <=
                        at(function.entry, 3); };
            }
            have to_integer(count(remaining(p))) == (to_integer(old(count(remaining(p)))) - 1) by {
                solve() using { -2147483648 <= (to_integer(old(count(remaining(p)))) - 1); (to_integer(old(count(remaining(p)))) - 1) <= 2147483647; };
            }
            known();
        }
        have to_integer(p->value) == (to_integer(old(p->value)) + 1) by {
            rewrite(at(function.entry, to_integer(p->value)), at(function.entry, (3 - to_integer(count(remaining(p))))));
            rewrite(to_integer(p->value), (3 - to_integer(count(remaining(p)))));
            rewrite(to_integer(count(remaining(p))), (to_integer(old(count(remaining(p)))) - 1));
            normalize();
        }
        known();
        known();
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
            solve() using { 0 <= to_integer(old(count(remaining(p)))); };
        }
        have (to_integer(old(count(remaining(p)))) + 3) <= 2147483647 by {
            solve() using { to_integer(old(count(remaining(p)))) == 0; };
        }
        have to_integer(count(remaining(p))) == (to_integer(old(count(remaining(p)))) + 3) by {
            solve() using { -2147483648 <= (to_integer(old(count(remaining(p)))) + 3); (to_integer(old(count(remaining(p)))) + 3) <= 2147483647; };
        }
        have to_integer(p->value) <= (3 - to_integer(count(remaining(p)))) by {
            solve() using { to_integer(count(remaining(p))) == (to_integer(old(count(remaining(p))))
                    + 3); to_integer(old(count(remaining(p)))) == 0; to_integer(p->value) == 0; };
        }
        have (3 - to_integer(count(remaining(p)))) <= to_integer(p->value) by {
            solve() using { to_integer(count(remaining(p))) == (to_integer(old(count(remaining(p))))
                    + 3); 0 <= to_integer(old(count(remaining(p)))); to_integer(p->value) == 0; };
        }
        solve() using { to_integer(p->value) <= (3 - to_integer(count(remaining(p)))); (3 - to_integer(count(remaining(p)))) <= to_integer(p->value); };
    }
    fold(control(p));
    step() by {
        solve() using { old((count(remaining(p)) as int32)) >= at(function.entry, 0); at(function.entry, to_integer(count(remaining(p)))) == at(function.entry, 0); };
    }
    step() by {
        solve() using { old((count(remaining(p)) as int32)) >= at(function.entry, 0); at(function.entry, to_integer(count(remaining(p)))) == at(function.entry, 0); };
    }
    unfold(control(p));
    unfold(remaining(p));
    unfold(authority(remaining(p)));
    step();
    known();
    have result == 2 by {
        known();
    }
    known();
}
```

```expect
pass
```
