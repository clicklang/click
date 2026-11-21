# Shared loop tests and updates retain the ranked backedge

The pre-test of the for loop and the post-test of the do-while each contain
one call. A continue reaches the for update or the do-while post-test before
the preservation proof can close. Each false path proves `n == 0` while
the call record is still available.

```c filename=shared_loop_test_and_update.c
int32 again(int32 n) { return n > 0; }

int32 shared_for(int32 n) {
    for (; again(n); n = n - 1) {
        continue;
    }
    return n;
}

int32 shared_do(int32 n) {
    do {
        n = n - 1;
        continue;
    } while (again(n));
    return n;
}
```

```click
verifying "shared_loop_test_and_update.c";

int32 again(int32 n) {
    ensures result == (if n > 0 { 1 } else { 0 });
}

int32 shared_for(int32 n) {
    requires n >= 0;
    ensures result == 0;
} by {
    step_until(loop(0).entry);
    loop {
        decreases n;
        invariant n >= 0;
        maintain by {
            step();
            have statement(0).call(again, 0).result ==
                (if at(statement(0).call(again, 0).entry, n) > 0 { 1 } else { 0 }) by solve();
            if statement(0).call(again, 0).result != 0 {
                have at(statement(0).call(again, 0).entry, n) > 0 by {
                    if at(statement(0).call(again, 0).entry, n) > 0 {
                        known();
                    } else {
                        have (if at(statement(0).call(again, 0).entry, n) > 0 { 1 } else { 0 }) == 0 by {
                            normalize() using { at(statement(0).call(again, 0).entry, n) <= 0; };
                        }
                        have statement(0).call(again, 0).result == 0 by {
                            solve() using {
                                statement(0).call(again, 0).result == (if at(statement(0).call(again, 0).entry, n) > 0 { 1 } else { 0 });
                                (if at(statement(0).call(again, 0).entry, n) > 0 { 1 } else { 0 }) == 0;
                            };
                        }
                        contradiction(statement(0).call(again, 0).result == 0);
                    }
                }
            } else {
                have n == 0 by {
                    have n >= 0 by known();
                    if n > 0 {
                        have to_integer(if n > 0 { 1 } else { 0 }) == 1 by {
                            solve() using { n > 0; };
                        }
                        have to_integer(statement(0).call(again, 0).result) == 1 by {
                            solve() using {
                                to_integer(statement(0).call(again, 0).result) == to_integer(if n > 0 { 1 } else { 0 });
                                to_integer(if n > 0 { 1 } else { 0 }) == 1;
                            };
                        }
                        have to_integer(statement(0).call(again, 0).result) == 0 by {
                            solve() using { statement(0).call(again, 0).result == 0; };
                        }
                        have 0 == 1 by {
                            solve() using {
                                to_integer(statement(0).call(again, 0).result) == 0;
                                to_integer(statement(0).call(again, 0).result) == 1;
                            };
                        }
                        contradiction(0 == 1);
                    } else {
                        solve() using { n >= 0; not(n > 0); };
                    }
                }
            }
        }
    }
    step();
    solve();
}

int32 shared_do(int32 n) {
    requires n > 0;
    ensures result == 0;
} by {
    step_until(loop(0).entry);
    loop {
        decreases n;
        invariant n > 0;
        maintain by {
            step();
            have n >= 0 by solve();
            step();
            step();
            have statement(0).call(again, 0).result ==
                (if at(statement(0).call(again, 0).entry, n) > 0 { 1 } else { 0 }) by solve();
            if statement(0).call(again, 0).result != 0 {
                have at(statement(0).call(again, 0).entry, n) > 0 by {
                    if at(statement(0).call(again, 0).entry, n) > 0 {
                        known();
                    } else {
                        have (if at(statement(0).call(again, 0).entry, n) > 0 { 1 } else { 0 }) == 0 by {
                            known();
                        }
                        have statement(0).call(again, 0).result == 0 by {
                            solve() using {
                                statement(0).call(again, 0).result == (if at(statement(0).call(again, 0).entry, n) > 0 { 1 } else { 0 });
                                (if at(statement(0).call(again, 0).entry, n) > 0 { 1 } else { 0 }) == 0;
                            };
                        }
                        contradiction(statement(0).call(again, 0).result == 0);
                    }
                }
            } else {
                have n == 0 by {
                    have n >= 0 by known();
                    if n > 0 {
                        have to_integer(if n > 0 { 1 } else { 0 }) == 1 by {
                            solve() using { n > 0; };
                        }
                        have to_integer(statement(0).call(again, 0).result) == 1 by {
                            solve() using {
                                to_integer(statement(0).call(again, 0).result) == to_integer(if n > 0 { 1 } else { 0 });
                                to_integer(if n > 0 { 1 } else { 0 }) == 1;
                            };
                        }
                        have to_integer(statement(0).call(again, 0).result) == 0 by {
                            solve() using { statement(0).call(again, 0).result == 0; };
                        }
                        have 0 == 1 by {
                            solve() using {
                                to_integer(statement(0).call(again, 0).result) == 0;
                                to_integer(statement(0).call(again, 0).result) == 1;
                            };
                        }
                        contradiction(0 == 1);
                    } else {
                        solve() using { n >= 0; not(n > 0); };
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
