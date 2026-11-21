# Integer range fold summation

The loop invariant tracks the exact prefix sum and bounds it using the element
range, which proves the intermediate machine addition stays within `int32`.
Initializedness is an explicit loop invariant. Its proof separates each selected
input cell from the stack locals and preserves it across the four setup steps
and two loop-body stores; instantiation supplies each required read. Ordinary
Integer congruence and order theorems compose the exact fold equalities.
At loop exit, `i <= n` together with `not i < n` establishes `i == n`; the
final proof rewrites that endpoint explicitly before returning so the exact
prefix invariant matches the full range in the postcondition.

```c filename=integer_sum_range_fold.c
int32 sum(int32 a[], int32 n) {
    int32 total;
    int32 i;
    total = 0;
    i = 0;
    while (i < n) {
        total = total + a[i];
        i = i + 1;
    }
    return total;
}
```

```click
import click::integer;
verifying "integer_sum_range_fold.c";

int32 sum(int32 a[], int32 n) {
    requires 0 <= n and n <= 1000;
    requires n <= 1073741823;
    requires viewable(a[0..n]);
    views a[0..n];
    requires forall (k: int32) {
        0 <= k and k < n implies
            -1000 <= a[k] and a[k] <= 1000
    };
    ensures result_sum: to_integer(result) ==
        (0..n).fold(0, |acc, k| { acc + to_integer(a[k]) });
} by {
    step();
    step();
    step();
    step();
    have 0 <= 0 by {
        known();
    }
    have (0..0).fold(0, |acc, k| { (acc + to_integer(a[k])) }) == 0 by {
        apply(integer_range_fold_empty((0..0).fold(0, |acc, k| { (acc + to_integer(a[k])) }))) using {
            0 <= 0;
        };
    }
    have 0 == (0..0).fold(0, |acc, k| { (acc + to_integer(a[k])) }) by {
        known();
    }
    have 0 <= (0..0).fold(0, |acc, k| { (acc + to_integer(a[k])) }) by {
        solve() using { (0..0).fold(0, |acc, k| { (acc + to_integer(a[k])) }) == 0; };
    }
    have (0..0).fold(0, |acc, k| { (acc + to_integer(a[k])) }) <= 0 by {
        solve() using { (0..0).fold(0, |acc, k| { (acc + to_integer(a[k])) }) == 0; };
    }
    have forall (j: int32) { 0 <= j and j < n implies defined(a[j]) } by {
        intro(); intro();
        instantiate(forall (k: int32) { 0 <= k and k < n implies defined(old(a[k])) }, j);
        have separate(memory(total), memory(a[j])) by { known(); }
        have separate(statement(0).footprint, memory(a[j])) by {
            solve() using { separate(memory(total), memory(a[j])); };
        }
        have at(statement(0).exit, defined(a[j])) by {
            preserve(memory(a[j]), statement(0));
        }
        have separate(memory(i), memory(a[j])) by { known(); }
        have separate(statement(1).footprint, memory(a[j])) by {
            solve() using { separate(memory(i), memory(a[j])); };
        }
        have at(statement(1).exit, defined(a[j])) by {
            preserve(memory(a[j]), statement(1));
        }
        have separate(statement(2).footprint, memory(a[j])) by {
            solve() using { separate(memory(total), memory(a[j])); };
        }
        have at(statement(2).exit, defined(a[j])) by {
            preserve(memory(a[j]), statement(2));
        }
        have separate(statement(3).footprint, memory(a[j])) by {
            solve() using { separate(memory(i), memory(a[j])); };
        }
        have at(statement(3).exit, defined(a[j])) by {
            preserve(memory(a[j]), statement(3));
        }
        known();
    }
    loop sum {
        decreases (n - i);
        invariant forall (j: int32) { 0 <= j and j < n implies defined(a[j]) };
        invariant 0 <= i;
        invariant i <= n;
        invariant to_integer(total) == (0..i).fold(0, |acc, k| { (acc + to_integer(a[k])) });
        invariant (-1000 * to_integer(i)) <= (0..i).fold(0, |acc, k| { (acc + to_integer(a[k])) });
        invariant (0..i).fold(0, |acc, k| { (acc + to_integer(a[k])) }) <= (1000 * to_integer(i));
        initialize by {
            have forall (j: int32) { 0 <= j and j < n implies defined(a[j]) } by { known(); }
            have 0 <= i by {
                known();
            }
            have i <= n by {
                if n < 1073741823 {
                    have n != 1073741823;
                    known();
                } else {
                    have n == 1073741823 by {
                        have n <= 1073741823 by {
                            known();
                        }
                        have n == 1073741823;
                        known();
                    }
                    rewrite(n, 1073741823);
                    known();
                }
            }
            have to_integer(total) == (0..i).fold(0, |acc, k| { (acc + to_integer(a[k])) }) by {
                known();
            }
            have (-1000 * to_integer(i)) <= (0..i).fold(0, |acc, k| { (acc + to_integer(a[k])) }) by {
                have -1000 * to_integer(i) <= 0 by { known(); }
                apply(click::integer::le_transitive(-1000 * to_integer(i), 0,
                    (0..i).fold(0, |acc, k| { acc + to_integer(a[k]) }))) using {
                    -1000 * to_integer(i) <= 0;
                    0 <= (0..i).fold(0, |acc, k| { acc + to_integer(a[k]) });
                };
            }
            have (0..i).fold(0, |acc, k| { (acc + to_integer(a[k])) }) <= (1000 * to_integer(i)) by {
                have 0 <= 1000 * to_integer(i) by { known(); }
                apply(click::integer::le_transitive(
                    (0..i).fold(0, |acc, k| { acc + to_integer(a[k]) }), 0,
                    1000 * to_integer(i))) using {
                    (0..i).fold(0, |acc, k| { acc + to_integer(a[k]) }) <= 0;
                    0 <= 1000 * to_integer(i);
                };
            }
        }
        maintain by {
            mark iter;
            have -1000 <= a[i] and a[i] <= 1000 by {
                instantiate(forall (k: int32) { 0 <= k and k < n implies -1000 <= a[k] and a[k] <= 1000 }, i);
                known();
            }
            have -1000 <= to_integer(a[i]);
            have to_integer(a[i]) <= 1000;
            have 0 <= to_integer(i);
            have to_integer(i) <= 1000 by {
                have to_integer(i) <= to_integer(n);
                have to_integer(n) <= 1000;
                solve() using { to_integer(i) <= to_integer(n); to_integer(n) <= 1000; };
            }
            have (-1000 * to_integer(i)) <= to_integer(total) by {
                have (-1000 * to_integer(i)) == (-1000 * to_integer(i)) by { known(); }
                apply(click::integer::le_substitute((-1000 * to_integer(i)), (0..i).fold(0, |acc, k| { (acc + to_integer(a[k])) }), (-1000 * to_integer(i)), to_integer(total))) using {
                    (-1000 * to_integer(i)) <= (0..i).fold(0, |acc, k| { (acc + to_integer(a[k])) });
                    (-1000 * to_integer(i)) == (-1000 * to_integer(i));
                    to_integer(total) == (0..i).fold(0, |acc, k| { (acc + to_integer(a[k])) });
                };
            }
            have to_integer(total) <= (1000 * to_integer(i)) by {
                have (1000 * to_integer(i)) == (1000 * to_integer(i)) by { known(); }
                apply(click::integer::le_substitute((0..i).fold(0, |acc, k| { (acc + to_integer(a[k])) }), (1000 * to_integer(i)), to_integer(total), (1000 * to_integer(i)))) using {
                    (0..i).fold(0, |acc, k| { (acc + to_integer(a[k])) }) <= (1000 * to_integer(i));
                    to_integer(total) == (0..i).fold(0, |acc, k| { (acc + to_integer(a[k])) });
                    (1000 * to_integer(i)) == (1000 * to_integer(i));
                };
            }
            have ((-1000 * to_integer(i)) - 1000) <= (to_integer(total) + to_integer(a[i])) by {
                solve() using { (-1000 * to_integer(i)) <= to_integer(total); -1000 <= to_integer(a[i]); };
            }
            have (to_integer(total) + to_integer(a[i])) >= -2147483648 by {
                solve() using { ((-1000 * to_integer(i)) - 1000) <= (to_integer(total) + to_integer(a[i])); to_integer(i) <= 1000; };
            }
            have (to_integer(total) + to_integer(a[i])) <= ((1000 * to_integer(i)) + 1000) by {
                solve() using { to_integer(total) <= (1000 * to_integer(i)); to_integer(a[i]) <= 1000; };
            }
            have (to_integer(total) + to_integer(a[i])) <= 2147483647 by {
                solve() using { (to_integer(total) + to_integer(a[i])) <= ((1000 * to_integer(i)) + 1000); to_integer(i) <= 1000; };
            }
            have defined(a[i]) by {
                instantiate(forall (j: int32) {
                    0 <= j and j < n implies defined(a[j])
                }, i);
                known();
            }
            have defined(old(a[i])) by {
                instantiate(forall (j: int32) { 0 <= j and j < n implies defined(old(a[j])) }, i);
                known();
            }
            have defined((total + a[i])) by {
                have defined(total + a[i]);
                all {
                    defined(load<int32>((a + i))) => {
                        known();
                    }
                    to_integer(total) + to_integer(a[i]) <= 2147483647 => { known(); }
                    to_integer(total) + to_integer(a[i]) >= -2147483648 => { known(); }
                }
            }
            have to_integer((total + a[i])) == (to_integer(total) + to_integer(a[i]));
            have to_integer(total + a[i]) == (0..i).fold(0, |acc, k| { (acc + to_integer(a[k])) }) + to_integer(a[i]) by {
                have to_integer(a[i]) == to_integer(a[i]) by { known(); }
                have to_integer(total) + to_integer(a[i]) == (0..i).fold(0, |acc, k| { (acc + to_integer(a[k])) }) + to_integer(a[i]) by {
                    apply(click::integer::equal_add(to_integer(total), (0..i).fold(0, |acc, k| { (acc + to_integer(a[k])) }), to_integer(a[i]), to_integer(a[i]))) using {
                        to_integer(total) == (0..i).fold(0, |acc, k| { (acc + to_integer(a[k])) }); to_integer(a[i]) == to_integer(a[i]);
                    };
                }
                known();
            }
            have i < 2147483647 by {
                have i < 1000;
                have 1000 < 2147483647 by {
                    known();
                }
                have i < 2147483647;
                known();
            }
            have defined((i + 1));
            have to_integer((i + 1)) == (to_integer(i) + to_integer(1));
            have (-1000 * to_integer((i + 1))) <= (to_integer(total) + to_integer(a[i])) by {
                solve() using { ((-1000 * to_integer(i)) - 1000) <= (to_integer(total) + to_integer(a[i])); to_integer((i + 1)) == (to_integer(i) + to_integer(1)); };
            }
            have (-1000 * to_integer((i + 1))) <= to_integer((total + a[i])) by {
                solve() using { (-1000 * to_integer((i + 1))) <= (to_integer(total) + to_integer(a[i])); to_integer((total + a[i])) == (to_integer(total) + to_integer(a[i])); };
            }
            have (to_integer(total) + to_integer(a[i])) <= (1000 * to_integer((i + 1))) by {
                solve() using { (to_integer(total) + to_integer(a[i])) <= ((1000 * to_integer(i)) + 1000); to_integer((i + 1)) == (to_integer(i) + to_integer(1)); };
            }
            have to_integer((total + a[i])) <= (1000 * to_integer((i + 1))) by {
                solve() using { to_integer((total + a[i])) == (to_integer(total) + to_integer(a[i])); (to_integer(total) + to_integer(a[i])) <= (1000 * to_integer((i + 1))); };
            }
            step();
            step();
            have forall (j: int32) { 0 <= j and j < n implies defined(a[j]) } by {
                intro(); intro();
                instantiate(at(iter, forall (j: int32) { 0 <= j and j < n implies defined(a[j]) }), j);
                have separate(memory(total), memory(a[j])) by { known(); }
                have separate(loop(0).statement(0).footprint, memory(a[j])) by {
                    solve() using { separate(memory(total), memory(a[j])); };
                }
                have at(loop(0).statement(0).exit, defined(a[j])) by {
                    preserve(memory(a[j]), loop(0).statement(0));
                }
                have separate(memory(i), memory(a[j])) by { known(); }
                have separate(loop(0).statement(1).footprint, memory(a[j])) by {
                    solve() using { separate(memory(i), memory(a[j])); };
                }
                have at(loop(0).statement(1).exit, defined(a[j])) by {
                    preserve(memory(a[j]), loop(0).statement(1));
                }
                known();
            }
            have to_integer(i) == to_integer((at(iter, i) + 1)) by {
                known();
            }
            have (0..(at(iter, i) + 1)).fold(0, |acc, k| { (acc + to_integer(a[k])) }) == ((0..at(iter, i)).fold(0, |acc, k| { (acc + to_integer(a[k])) }) + to_integer(a[at(iter, i)])) by {
                apply(integer_range_fold_append((0..at(iter, i)).fold(0, |acc, k| { (acc + to_integer(a[k])) }))) using {
                    0 <= at(iter, i);
                    at(iter, i) < n;
                    at(iter, i) < 2147483647;
                    viewable(a[0..n]);
                    0 <= n;
                    n <= 1073741823;
                    forall (k: int32) { 0 <= k and k < n implies -1000 <= a[k] and a[k] <= 1000 };
                };
            }
            have 0 <= i;
            have i <= n;
            have to_integer(total) == (0..(at(iter, i) + 1)).fold(0, |acc, k| { (acc + to_integer(a[k])) }) by {
                have (0..(at(iter, i) + 1)).fold(0, |acc, k| { (acc + to_integer(a[k])) }) == (0..(at(iter, i) + 1)).fold(0, |acc, k| { (acc + to_integer(a[k])) }) by { known(); }
                have (0..(at(iter, i) + 1)).fold(0, |acc, k| { (acc + to_integer(a[k])) }) == to_integer(total) by {
                    apply(click::integer::equal_substitute((0..(at(iter, i) + 1)).fold(0, |acc, k| { (acc + to_integer(a[k])) }), ((0..at(iter, i)).fold(0, |acc, k| { (acc + to_integer(a[k])) }) + to_integer(a[at(iter, i)])), (0..(at(iter, i) + 1)).fold(0, |acc, k| { (acc + to_integer(a[k])) }), to_integer(total))) using {
                        (0..(at(iter, i) + 1)).fold(0, |acc, k| { (acc + to_integer(a[k])) }) == ((0..at(iter, i)).fold(0, |acc, k| { (acc + to_integer(a[k])) }) + to_integer(a[at(iter, i)]));
                        (0..(at(iter, i) + 1)).fold(0, |acc, k| { (acc + to_integer(a[k])) }) == (0..(at(iter, i) + 1)).fold(0, |acc, k| { (acc + to_integer(a[k])) });
                        to_integer(total) == ((0..at(iter, i)).fold(0, |acc, k| { (acc + to_integer(a[k])) }) + to_integer(a[at(iter, i)]));
                    };
                }
                known();
            }
            have to_integer(total) == (0..i).fold(0, |acc, k| { (acc + to_integer(a[k])) }) by {
                rewrite(to_integer(i), to_integer((at(iter, i) + 1)));
                known();
            }
            have (-1000 * to_integer(i)) <= (0..i).fold(0, |acc, k| { (acc + to_integer(a[k])) }) by {
                solve() using { (-1000 * to_integer(i)) <= to_integer(total); to_integer(total) == (0..i).fold(0, |acc, k| { (acc + to_integer(a[k])) }); };
            }
            have (0..i).fold(0, |acc, k| { (acc + to_integer(a[k])) }) <= (1000 * to_integer(i)) by {
                solve() using { to_integer(total) <= (1000 * to_integer(i)); to_integer(total) == (0..i).fold(0, |acc, k| { (acc + to_integer(a[k])) }); };
            }
            have forall (k: int32) { k >= 0 and k < i implies defined(a[k]) } by {
                intro();
                intro();
                have k < n;
                instantiate(forall (j: int32) {
                    0 <= j and j < n implies defined(a[j])
                }, k);
                known();
            }
            have to_integer(i) <= to_integer(n);
            have to_integer(i) == (to_integer(at(iter, i)) + 1) by {
                solve() using {
                    to_integer(i) == to_integer((at(iter, i) + 1));
                    to_integer((at(iter, i) + 1)) == (to_integer(at(iter, i)) + to_integer(1));
                };
            }
        }
        otherwise {
            have to_integer(total) == (0..i).fold(0, |acc, k| { acc + to_integer(a[k]) }) by known();
        }
    }
    have i == n;
    have n == i by {
        rewrite(n, i);
        known();
    }
    have to_integer(total) == (0..n).fold(0, |acc, k| { (acc + to_integer(a[k])) }) by {
        rewrite(n, i);
        known();
    }
    step();
    have to_integer(result) == (0..n).fold(0, |acc, k| { (acc + to_integer(a[k])) }) by {
        known();
    }
    known();
}
```

```expect
pass
```
