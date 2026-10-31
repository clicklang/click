# Integer range fold summation

The loop invariant tracks the exact prefix sum and bounds it using the element
range, which proves the intermediate machine addition stays within `int32`.
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
        normalize();
    }
    have (0..0).fold(0, |acc, k| { (acc + to_integer(a[k])) }) == 0 by {
        apply(integer_range_fold_empty((0..0).fold(0, |acc, k| { (acc + to_integer(a[k])) }))) using {
            0 <= 0;
        };
    }
    have 0 == (0..0).fold(0, |acc, k| { (acc + to_integer(a[k])) }) by {
        normalize() using {
            (0..0).fold(0, |acc, k| { (acc + to_integer(a[k])) }) == 0;
        };
    }
    have 0 <= (0..0).fold(0, |acc, k| { (acc + to_integer(a[k])) }) by {
        arithmetic_certificate {
            premise 0: (0..0).fold(0, |acc, k| { (acc + to_integer(a[k])) }) == 0 => (0..0).fold(0, |acc, k| { (acc + to_integer(a[k])) }) == 0;
            less_equal_from_equal 0 reverse => 0 <= (0..0).fold(0, |acc, k| { (acc + to_integer(a[k])) });
            conclusion 1;
        }
    }
    have (0..0).fold(0, |acc, k| { (acc + to_integer(a[k])) }) <= 0 by {
        arithmetic_certificate {
            premise 0: (0..0).fold(0, |acc, k| { (acc + to_integer(a[k])) }) == 0 => (0..0).fold(0, |acc, k| { (acc + to_integer(a[k])) }) == 0;
            less_equal_from_equal 0 => (0..0).fold(0, |acc, k| { (acc + to_integer(a[k])) }) <= 0;
            conclusion 1;
        }
    }
    loop as sum {
        decreases (n - i);
        invariant 0 <= i;
        invariant i <= n;
        invariant to_integer(total) == (0..i).fold(0, |acc, k| { (acc + to_integer(a[k])) });
        invariant (-1000 * to_integer(i)) <= (0..i).fold(0, |acc, k| { (acc + to_integer(a[k])) });
        invariant (0..i).fold(0, |acc, k| { (acc + to_integer(a[k])) }) <= (1000 * to_integer(i));
        initialize by {
            have 0 <= i by {
                normalize();
            }
            have i <= n by {
                if n < 1073741823 {
                    have n != 1073741823;
                    assumption();
                } else {
                    have n == 1073741823 by {
                        have n <= 1073741823 by {
                            assumption();
                        }
                        have n == 1073741823;
                        assumption();
                    }
                    rewrite(n == 1073741823);
                    normalize();
                }
            }
            have to_integer(total) == (0..i).fold(0, |acc, k| { (acc + to_integer(a[k])) }) by {
                assumption();
            }
            have (-1000 * to_integer(i)) <= (0..i).fold(0, |acc, k| { (acc + to_integer(a[k])) }) by {
                have (-1000 * to_integer(i)) == 0 by {
                    normalize();
                }
                arithmetic_certificate {
                    premise 0: (-1000 * to_integer(i)) == 0 => (-1000 * to_integer(i)) == 0;
                    less_equal_from_equal 0 => (-1000 * to_integer(i)) <= 0;
                    premise 1: 0 <= (0..i).fold(0, |acc, k| { (acc + to_integer(a[k])) }) => 0 <= (0..i).fold(0, |acc, k| { (acc + to_integer(a[k])) });
                    add 1, 2 => ((-1000 * to_integer(i)) + 0) <= (0 + (0..i).fold(0, |acc, k| { (acc + to_integer(a[k])) }));
                    conclusion 3;
                }
            }
            have (0..i).fold(0, |acc, k| { (acc + to_integer(a[k])) }) <= (1000 * to_integer(i)) by {
                have (1000 * to_integer(i)) == 0 by {
                    normalize();
                }
                arithmetic_certificate {
                    premise 0: (1000 * to_integer(i)) == 0 => (1000 * to_integer(i)) == 0;
                    less_equal_from_equal 0 reverse => 0 <= (1000 * to_integer(i));
                    premise 1: (0..i).fold(0, |acc, k| { (acc + to_integer(a[k])) }) <= 0 => (0..i).fold(0, |acc, k| { (acc + to_integer(a[k])) }) <= 0;
                    add 2, 1 => ((0..i).fold(0, |acc, k| { (acc + to_integer(a[k])) }) + 0) <= (0 + (1000 * to_integer(i)));
                    conclusion 3;
                }
            }
        }
        preserve by {
            have -1000 <= a[i] and a[i] <= 1000 by {
                instantiate(forall (k: int32) { 0 <= k and k < n implies -1000 <= a[k] and a[k] <= 1000 }, i);
                assumption();
            }
            have -1000 <= to_integer(a[i]);
            have to_integer(a[i]) <= 1000;
            have 0 <= to_integer(i);
            have to_integer(i) <= 1000 by {
                have to_integer(i) <= to_integer(n);
                have to_integer(n) <= 1000;
                arithmetic_certificate {
                    premise 0: to_integer(i) <= to_integer(n) => to_integer(i) <= to_integer(n);
                    premise 1: to_integer(n) <= 1000 => to_integer(n) <= 1000;
                    add 0, 1 => (to_integer(i) + to_integer(n)) <= (to_integer(n) + 1000);
                    conclusion 2;
                }
            }
            have (-1000 * to_integer(i)) <= to_integer(total) by {
                arithmetic_certificate {
                    premise 0: to_integer(total) == (0..i).fold(0, |acc, k| { (acc + to_integer(a[k])) }) => to_integer(total) == (0..i).fold(0, |acc, k| { (acc + to_integer(a[k])) });
                    less_equal_from_equal 0 reverse => (0..i).fold(0, |acc, k| { (acc + to_integer(a[k])) }) <= to_integer(total);
                    premise 1: (-1000 * to_integer(i)) <= (0..i).fold(0, |acc, k| { (acc + to_integer(a[k])) }) => (-1000 * to_integer(i)) <= (0..i).fold(0, |acc, k| { (acc + to_integer(a[k])) });
                    add 1, 2 => ((0..i).fold(0, |acc, k| { (acc + to_integer(a[k])) }) + (-1000 * to_integer(i))) <= (to_integer(total) + (0..i).fold(0, |acc, k| { (acc + to_integer(a[k])) }));
                    conclusion 3;
                }
            }
            have to_integer(total) <= (1000 * to_integer(i)) by {
                arithmetic_certificate {
                    premise 0: to_integer(total) == (0..i).fold(0, |acc, k| { (acc + to_integer(a[k])) }) => to_integer(total) == (0..i).fold(0, |acc, k| { (acc + to_integer(a[k])) });
                    less_equal_from_equal 0 => to_integer(total) <= (0..i).fold(0, |acc, k| { (acc + to_integer(a[k])) });
                    premise 1: (0..i).fold(0, |acc, k| { (acc + to_integer(a[k])) }) <= (1000 * to_integer(i)) => (0..i).fold(0, |acc, k| { (acc + to_integer(a[k])) }) <= (1000 * to_integer(i));
                    add 1, 2 => (to_integer(total) + (0..i).fold(0, |acc, k| { (acc + to_integer(a[k])) })) <= ((0..i).fold(0, |acc, k| { (acc + to_integer(a[k])) }) + (1000 * to_integer(i)));
                    conclusion 3;
                }
            }
            have ((-1000 * to_integer(i)) - 1000) <= (to_integer(total) + to_integer(a[i])) by {
                arithmetic_certificate {
                    premise 0: (-1000 * to_integer(i)) <= to_integer(total) => (-1000 * to_integer(i)) <= to_integer(total);
                    premise 1: -1000 <= to_integer(a[i]) => -1000 <= to_integer(a[i]);
                    add 0, 1 => ((-1000 * to_integer(i)) + -1000) <= (to_integer(total) + to_integer(a[i]));
                    conclusion 2;
                }
            }
            have (to_integer(total) + to_integer(a[i])) >= -2147483648 by {
                arithmetic_certificate {
                    premise 0: ((-1000 * to_integer(i)) - 1000) <= (to_integer(total) + to_integer(a[i])) => ((-1000 * to_integer(i)) - 1000) <= (to_integer(total) + to_integer(a[i]));
                    premise 1: to_integer(i) <= 1000 => to_integer(i) <= 1000;
                    scale 1 by 1000 => (1000 * to_integer(i)) <= to_integer((1000 * 1000));
                    add 0, 2 => (((-1000 * to_integer(i)) - 1000) + (1000 * to_integer(i))) <= ((to_integer(total) + to_integer(a[i])) + (1000 * 1000));
                    trivial => -2146482648 <= 0;
                    add 3, 4 => ((((-1000 * to_integer(i)) - 1000) + (1000 * to_integer(i))) + -2146482648) <= (((to_integer(total) + to_integer(a[i])) + (1000 * 1000)) + 0);
                    conclusion 5;
                }
            }
            have (to_integer(total) + to_integer(a[i])) <= ((1000 * to_integer(i)) + 1000) by {
                arithmetic_certificate {
                    premise 0: to_integer(total) <= (1000 * to_integer(i)) => to_integer(total) <= (1000 * to_integer(i));
                    premise 1: to_integer(a[i]) <= 1000 => to_integer(a[i]) <= 1000;
                    add 0, 1 => (to_integer(total) + to_integer(a[i])) <= ((1000 * to_integer(i)) + 1000);
                    conclusion 2;
                }
            }
            have (to_integer(total) + to_integer(a[i])) <= 2147483647 by {
                arithmetic_certificate {
                    premise 0: (to_integer(total) + to_integer(a[i])) <= ((1000 * to_integer(i)) + 1000) => (to_integer(total) + to_integer(a[i])) <= ((1000 * to_integer(i)) + 1000);
                    premise 1: to_integer(i) <= 1000 => to_integer(i) <= 1000;
                    scale 1 by 1000 => (1000 * to_integer(i)) <= to_integer((1000 * 1000));
                    add 0, 2 => ((to_integer(total) + to_integer(a[i])) + (1000 * to_integer(i))) <= (((1000 * to_integer(i)) + 1000) + (1000 * 1000));
                    trivial => -2146482647 <= 0;
                    add 3, 4 => (((to_integer(total) + to_integer(a[i])) + (1000 * to_integer(i))) + -2146482647) <= ((((1000 * to_integer(i)) + 1000) + (1000 * 1000)) + 0);
                    conclusion 5;
                }
            }
            have defined(a[i]) by {
                transport(viewable(a[0..n]), defined(a[i])) using {
                    viewable(a[0..n]);
                    0 <= n;
                    n <= 1073741823;
                    0 <= i;
                    i < n;
                };
            }
            have defined((total + a[i])) by {
                have defined(total + a[i]);
                both {
                    assumption();
                } and {
                    assumption();
                }
            }
            have to_integer((total + a[i])) == (to_integer(total) + to_integer(a[i]));
            have to_integer((total + a[i])) == ((0..i).fold(0, |acc, k| { (acc + to_integer(a[k])) }) + to_integer(a[i])) by {
                arithmetic_certificate {
                    premise 0: to_integer((total + a[i])) == (to_integer(total) + to_integer(a[i])) => to_integer((total + a[i])) == (to_integer(total) + to_integer(a[i]));
                    premise 1: to_integer(total) == (0..i).fold(0, |acc, k| { (acc + to_integer(a[k])) }) => to_integer(total) == (0..i).fold(0, |acc, k| { (acc + to_integer(a[k])) });
                    add 0, 1 => (to_integer((total + a[i])) + to_integer(total)) == ((to_integer(total) + to_integer(a[i])) + (0..i).fold(0, |acc, k| { (acc + to_integer(a[k])) }));
                    conclusion 2;
                }
            }
            have i < 2147483647 by {
                have i < 1000;
                have 1000 < 2147483647 by {
                    normalize();
                }
                have i < 2147483647;
                assumption();
            }
            have defined((i + 1));
            have to_integer((i + 1)) == (to_integer(i) + to_integer(1));
            have (-1000 * to_integer((i + 1))) <= (to_integer(total) + to_integer(a[i])) by {
                arithmetic_certificate {
                    premise 0: ((-1000 * to_integer(i)) - 1000) <= (to_integer(total) + to_integer(a[i])) => ((-1000 * to_integer(i)) - 1000) <= (to_integer(total) + to_integer(a[i]));
                    premise 1: to_integer((i + 1)) == (to_integer(i) + to_integer(1)) => to_integer((i + 1)) == (to_integer(i) + to_integer(1));
                    less_equal_from_equal 1 reverse => (to_integer(i) + to_integer(1)) <= to_integer((i + 1));
                    scale 2 by 1000 => (1000 * (to_integer(i) + to_integer(1))) <= (1000 * to_integer((i + 1)));
                    add 0, 3 => (((-1000 * to_integer(i)) - 1000) + (1000 * (to_integer(i) + to_integer(1)))) <= ((to_integer(total) + to_integer(a[i])) + (1000 * to_integer((i + 1))));
                    conclusion 4;
                }
            }
            have (-1000 * to_integer((i + 1))) <= to_integer((total + a[i])) by {
                arithmetic_certificate {
                    premise 0: (-1000 * to_integer((i + 1))) <= (to_integer(total) + to_integer(a[i])) => (-1000 * to_integer((i + 1))) <= (to_integer(total) + to_integer(a[i]));
                    premise 1: to_integer((total + a[i])) == (to_integer(total) + to_integer(a[i])) => to_integer((total + a[i])) == (to_integer(total) + to_integer(a[i]));
                    less_equal_from_equal 1 reverse => (to_integer(total) + to_integer(a[i])) <= to_integer((total + a[i]));
                    add 0, 2 => ((-1000 * to_integer((i + 1))) + (to_integer(total) + to_integer(a[i]))) <= ((to_integer(total) + to_integer(a[i])) + to_integer((total + a[i])));
                    conclusion 3;
                }
            }
            have (to_integer(total) + to_integer(a[i])) <= (1000 * to_integer((i + 1))) by {
                arithmetic_certificate {
                    premise 0: (to_integer(total) + to_integer(a[i])) <= ((1000 * to_integer(i)) + 1000) => (to_integer(total) + to_integer(a[i])) <= ((1000 * to_integer(i)) + 1000);
                    premise 1: to_integer((i + 1)) == (to_integer(i) + to_integer(1)) => to_integer((i + 1)) == (to_integer(i) + to_integer(1));
                    less_equal_from_equal 1 reverse => (to_integer(i) + to_integer(1)) <= to_integer((i + 1));
                    scale 2 by 1000 => (1000 * (to_integer(i) + to_integer(1))) <= (1000 * to_integer((i + 1)));
                    add 0, 3 => ((to_integer(total) + to_integer(a[i])) + (1000 * (to_integer(i) + to_integer(1)))) <= (((1000 * to_integer(i)) + 1000) + (1000 * to_integer((i + 1))));
                    conclusion 4;
                }
            }
            have to_integer((total + a[i])) <= (1000 * to_integer((i + 1))) by {
                arithmetic_certificate {
                    premise 0: to_integer((total + a[i])) == (to_integer(total) + to_integer(a[i])) => to_integer((total + a[i])) == (to_integer(total) + to_integer(a[i]));
                    less_equal_from_equal 0 => to_integer((total + a[i])) <= (to_integer(total) + to_integer(a[i]));
                    premise 1: (to_integer(total) + to_integer(a[i])) <= (1000 * to_integer((i + 1))) => (to_integer(total) + to_integer(a[i])) <= (1000 * to_integer((i + 1)));
                    add 1, 2 => (to_integer((total + a[i])) + (to_integer(total) + to_integer(a[i]))) <= ((to_integer(total) + to_integer(a[i])) + (1000 * to_integer((i + 1))));
                    conclusion 3;
                }
            }
            step();
            step();
            have to_integer(i) == to_integer((at(region(5).entry, i) + 1)) by {
                normalize();
            }
            have (0..(at(region(5).entry, i) + 1)).fold(0, |acc, k| { (acc + to_integer(a[k])) }) == ((0..at(region(5).entry, i)).fold(0, |acc, k| { (acc + to_integer(a[k])) }) + to_integer(a[at(region(5).entry, i)])) by {
                apply(integer_range_fold_append((0..at(region(5).entry, i)).fold(0, |acc, k| { (acc + to_integer(a[k])) }))) using {
                    0 <= at(region(5).entry, i);
                    at(region(5).entry, i) < n;
                    at(region(5).entry, i) < 2147483647;
                    viewable(a[0..n]);
                    0 <= n;
                    n <= 1073741823;
                    forall (k: int32) { 0 <= k and k < n implies -1000 <= a[k] and a[k] <= 1000 };
                };
            }
            have 0 <= i;
            have i <= n;
            have to_integer(total) == (0..(at(region(5).entry, i) + 1)).fold(0, |acc, k| { (acc + to_integer(a[k])) }) by {
                arithmetic_certificate {
                    premise 0: to_integer(total) == ((0..at(region(5).entry, i)).fold(0, |acc, k| { (acc + to_integer(a[k])) }) + to_integer(a[at(region(5).entry, i)])) => to_integer(total) == ((0..at(region(5).entry, i)).fold(0, |acc, k| { (acc + to_integer(a[k])) }) + to_integer(a[at(region(5).entry, i)]));
                    premise 1: (0..(at(region(5).entry, i) + 1)).fold(0, |acc, k| { (acc + to_integer(a[k])) }) == ((0..at(region(5).entry, i)).fold(0, |acc, k| { (acc + to_integer(a[k])) }) + to_integer(a[at(region(5).entry, i)])) => (0..(at(region(5).entry, i) + 1)).fold(0, |acc, k| { (acc + to_integer(a[k])) }) == ((0..at(region(5).entry, i)).fold(0, |acc, k| { (acc + to_integer(a[k])) }) + to_integer(a[at(region(5).entry, i)]));
                    scale 1 by -1 => (-1 * (0..(at(region(5).entry, i) + 1)).fold(0, |acc, k| { (acc + to_integer(a[k])) })) == (-1 * ((0..at(region(5).entry, i)).fold(0, |acc, k| { (acc + to_integer(a[k])) }) + to_integer(a[at(region(5).entry, i)])));
                    add 0, 2 => (to_integer(total) + (-1 * (0..(at(region(5).entry, i) + 1)).fold(0, |acc, k| { (acc + to_integer(a[k])) }))) == (((0..at(region(5).entry, i)).fold(0, |acc, k| { (acc + to_integer(a[k])) }) + to_integer(a[at(region(5).entry, i)])) + (-1 * ((0..at(region(5).entry, i)).fold(0, |acc, k| { (acc + to_integer(a[k])) }) + to_integer(a[at(region(5).entry, i)]))));
                    conclusion 3;
                }
            }
            have to_integer(total) == (0..i).fold(0, |acc, k| { (acc + to_integer(a[k])) }) by {
                rewrite(to_integer(i) == to_integer((at(region(5).entry, i) + 1)));
                assumption();
            }
            have (-1000 * to_integer(i)) <= (0..i).fold(0, |acc, k| { (acc + to_integer(a[k])) }) by {
                arithmetic_certificate {
                    premise 0: (-1000 * to_integer(i)) <= to_integer(total) => (-1000 * to_integer(i)) <= to_integer(total);
                    premise 1: to_integer(total) == (0..i).fold(0, |acc, k| { (acc + to_integer(a[k])) }) => to_integer(total) == (0..i).fold(0, |acc, k| { (acc + to_integer(a[k])) });
                    less_equal_from_equal 1 => to_integer(total) <= (0..i).fold(0, |acc, k| { (acc + to_integer(a[k])) });
                    add 0, 2 => ((-1000 * to_integer(i)) + to_integer(total)) <= (to_integer(total) + (0..i).fold(0, |acc, k| { (acc + to_integer(a[k])) }));
                    conclusion 3;
                }
            }
            have (0..i).fold(0, |acc, k| { (acc + to_integer(a[k])) }) <= (1000 * to_integer(i)) by {
                arithmetic_certificate {
                    premise 0: to_integer(total) <= (1000 * to_integer(i)) => to_integer(total) <= (1000 * to_integer(i));
                    premise 1: to_integer(total) == (0..i).fold(0, |acc, k| { (acc + to_integer(a[k])) }) => to_integer(total) == (0..i).fold(0, |acc, k| { (acc + to_integer(a[k])) });
                    less_equal_from_equal 1 reverse => (0..i).fold(0, |acc, k| { (acc + to_integer(a[k])) }) <= to_integer(total);
                    add 0, 2 => (to_integer(total) + (0..i).fold(0, |acc, k| { (acc + to_integer(a[k])) })) <= ((1000 * to_integer(i)) + to_integer(total));
                    conclusion 3;
                }
            }
            have forall (k: int32) { k >= 0 and k < i implies defined(a[k]) } by {
                intro();
                intro();
                have k < n;
                transport(viewable(a[0..n]), defined(a[k])) using {
                    viewable(a[0..n]);
                    0 <= n;
                    n <= 1073741823;
                    k >= 0;
                    k < n;
                };
            }
            have to_integer(i) <= to_integer(n);
            have to_integer(i) == (to_integer(at(region(5).entry, i)) + 1) by {
                normalize() using {
                    to_integer(i) == to_integer((at(region(5).entry, i) + 1));
                    to_integer((at(region(5).entry, i) + 1)) == (to_integer(at(region(5).entry, i)) + to_integer(1));
                };
            }
            close_invariants() by {
                both {
                    assumption();
                } and {
                    both {
                        intro();
                        assumption();
                    } and {
                        both {
                            intro();
                            intro();
                            assumption();
                        } and {
                            both {
                                arithmetic_certificate {
                                    premise 0: to_integer(i) <= to_integer(n) => to_integer(i) <= to_integer(n);
                                    conclusion 0;
                                }
                            } and {
                                arithmetic_certificate {
                                    premise 0: to_integer(i) == (to_integer(at(region(5).entry, i)) + 1) => to_integer(i) == (to_integer(at(region(5).entry, i)) + 1);
                                    less_equal_from_equal 0 reverse => (to_integer(at(region(5).entry, i)) + 1) <= to_integer(i);
                                    trivial => 0 < 1;
                                    add 1, 2 => ((to_integer(at(region(5).entry, i)) + 1) + 0) < (to_integer(i) + 1);
                                    conclusion 3;
                                }
                            }
                        }
                    }
                }
            }
        }
    }
    have i == n;
    have n == i by {
        rewrite(n == i);
        normalize();
    }
    have to_integer(total) == (0..n).fold(0, |acc, k| { (acc + to_integer(a[k])) }) by {
        rewrite(n == i);
        assumption();
    }
    step();
    have to_integer(result) == (0..n).fold(0, |acc, k| { (acc + to_integer(a[k])) }) by {
        assumption();
    }
    assumption();
}
```

```expect
pass
```
