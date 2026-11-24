import click::integer;

function unmarked(v: int32[], lo: int32, hi: int32) -> Integer {
    (lo..hi).fold(0, |acc, k| { acc + to_integer(if v[k] == 0 { 1 } else { 0 }) })
}

theorem unmarked_nonnegative(v: int32[], lo: int32, n: int32, hi: int32) {
    requires 0 <= lo;
    requires 0 <= hi;
    requires hi <= n;
    requires n <= 1073741823;
    views v[lo..n];
    ensures 0 <= unmarked(v, lo, hi) by {
        let ih = induct(hi);
        if hi <= lo {
            unfold(unmarked(v, lo, hi));
            close();
        } else {
            have 0 <= to_integer(hi - 1) by { close() using { 0 <= lo; lo < hi; }; }
            have to_integer(hi - 1) < to_integer(hi) by { close() using { 0 <= lo; lo < hi; }; }
            have to_integer(hi - 1) <= to_integer(n) by { close() using { 0 <= lo; lo < hi; hi <= n; }; }
            apply(ih(hi - 1));
            have to_integer(lo) <= to_integer(hi - 1) by { close() using { 0 <= lo; lo < hi; }; }
            have to_integer(hi - 1) < 2147483647 by { close() using { 0 <= lo; lo < hi; }; }
            unfold(unmarked(v, lo, hi));
            have 0 <= (if v[hi - 1] == 0 { 1 } else { 0 });
            have to_integer(0) <= to_integer((if v[hi - 1] == 0 { 1 } else { 0 }));
            have 0 <= unmarked(v, lo, hi - 1)
                + to_integer(if v[hi - 1] == 0 { 1 } else { 0 }) by {
                close() using {
                    0 <= unmarked(v, lo, hi - 1);
                    to_integer(0) <= to_integer(if v[hi - 1] == 0 { 1 } else { 0 });
                };
            }
            close();
        }
    }
}

theorem unmarked_frame(
    a: int32[],
    b: int32[],
    lo: int32,
    n: int32,
    m: int32,
    hi: int32
) {
    requires 0 <= lo;
    requires 0 <= hi;
    requires hi <= m;
    requires m <= n;
    requires n <= 1073741823;
    views a[lo..n];
    views b[lo..n];
    requires forall (k: int32) {
        lo <= k and k < m implies a[k] == b[k]
    };
    ensures unmarked(a, lo, hi) == unmarked(b, lo, hi) by {
        let ih = induct(hi);
        if hi <= lo {
            unfold(unmarked(a, lo, hi));
            unfold(unmarked(b, lo, hi));
            close();
        } else {
            have 0 <= to_integer(hi - 1) by { close() using { 0 <= lo; lo < hi; }; }
            have to_integer(hi - 1) < to_integer(hi) by { close() using { 0 <= lo; lo < hi; }; }
            have to_integer(lo) <= to_integer(hi - 1) by { close() using { 0 <= lo; lo < hi; }; }
            have to_integer(hi - 1) <= to_integer(m) by { close() using { 0 <= lo; lo < hi; hi <= m; }; }
            have to_integer(hi - 1) < to_integer(m) by { close() using { 0 <= lo; lo < hi; hi <= m; }; }
            have to_integer(hi - 1) < 2147483647 by { close() using { 0 <= lo; lo < hi; }; }
            apply(ih(hi - 1));
            have a[hi - 1] == b[hi - 1] by {
                have lo <= (hi - 1) and (hi - 1) < m;
                instantiate(forall (k: int32) {
                    lo <= k and k < m implies a[k] == b[k]
                }, hi - 1);
                close();
            }
            unfold(unmarked(a, lo, hi));
            unfold(unmarked(b, lo, hi));
            have to_integer(if a[hi - 1] == 0 { 1 } else { 0 })
                == to_integer(if b[hi - 1] == 0 { 1 } else { 0 }) by {
                close() using { a[hi - 1] == b[hi - 1]; };
            }
            have unmarked(a, lo, hi - 1)
                + to_integer(if a[hi - 1] == 0 { 1 } else { 0 })
                == unmarked(b, lo, hi - 1)
                    + to_integer(if b[hi - 1] == 0 { 1 } else { 0 }) by {
                close() using {
                    unmarked(a, lo, hi - 1) == unmarked(b, lo, hi - 1);
                    to_integer(if a[hi - 1] == 0 { 1 } else { 0 })
                        == to_integer(if b[hi - 1] == 0 { 1 } else { 0 });
                };
            }
            close();
        }
    }
}

theorem unmarked_point_update(
    a: int32[],
    b: int32[],
    lo: int32,
    n: int32,
    hi: int32,
    j: int32
) {
    requires 0 <= lo;
    requires 0 <= hi;
    requires hi <= n;
    requires n <= 1073741823;
    views a[lo..n];
    views b[lo..n];
    requires lo <= j;
    requires j < hi;
    requires a[j] == 0;
    requires b[j] != 0;
    requires forall (k: int32) {
        lo <= k and k < j implies a[k] == b[k]
    };
    requires forall (k: int32) {
        j < k and k < n implies a[k] == b[k]
    };
    ensures unmarked(b, lo, hi) == unmarked(a, lo, hi) - 1 by {
        let ih = induct(hi);
        if hi <= lo {
            have j < lo by { close() using { j < hi; hi <= lo; }; }
            contradiction(lo <= j);
        } else {
            have 0 <= to_integer(hi - 1) by { close() using { 0 <= lo; lo < hi; }; }
            have to_integer(hi - 1) < to_integer(hi) by { close() using { 0 <= lo; lo < hi; }; }
            have to_integer(lo) <= to_integer(hi - 1) by { close() using { 0 <= lo; lo < hi; }; }
            have to_integer(hi - 1) <= to_integer(n) by { close() using { 0 <= lo; lo < hi; hi <= n; }; }
            have to_integer(hi - 1) < to_integer(n) by { close() using { 0 <= lo; lo < hi; hi <= n; }; }
            have to_integer(hi - 1) < 2147483647 by { close() using { 0 <= lo; lo < hi; }; }
            have to_integer(j) <= to_integer(hi - 1) by { close() using { 0 <= lo; lo < hi; j < hi; }; }
            if to_integer(j) == to_integer(hi - 1) {
                have j <= n by { close() using { j < hi; hi <= n; }; }
                have to_integer(hi - 1) <= to_integer(j) by {
                    close() using { 0 <= lo; lo < hi; to_integer(j) == to_integer(hi - 1); };
                }
                apply(unmarked_frame(a, b, lo, n, j, hi - 1));
                have a[hi - 1] == 0 by { close() using { a[j] == 0; to_integer(j) == to_integer(hi - 1); }; }
                have b[hi - 1] != 0 by { close() using { b[j] != 0; to_integer(j) == to_integer(hi - 1); }; }
                unfold(unmarked(a, lo, hi));
                unfold(unmarked(b, lo, hi));
                have (if a[hi - 1] == 0 { 1 } else { 0 }) == 1 by {
                    close();
                }
                have (if b[hi - 1] == 0 { 1 } else { 0 }) == 0 by {
                    close();
                }
                have to_integer(if a[hi - 1] == 0 { 1 } else { 0 }) == 1 by {
                    close() using { (if a[hi - 1] == 0 { 1 } else { 0 }) == 1; };
                }
                have to_integer(if b[hi - 1] == 0 { 1 } else { 0 }) == 0 by {
                    close() using { (if b[hi - 1] == 0 { 1 } else { 0 }) == 0; };
                }
                have unmarked(b, lo, hi - 1)
                    + to_integer(if b[hi - 1] == 0 { 1 } else { 0 })
                    == unmarked(a, lo, hi - 1)
                        + to_integer(if a[hi - 1] == 0 { 1 } else { 0 }) - 1 by {
                    close() using {
                        unmarked(a, lo, hi - 1) == unmarked(b, lo, hi - 1);
                        to_integer(if a[hi - 1] == 0 { 1 } else { 0 }) == 1;
                        to_integer(if b[hi - 1] == 0 { 1 } else { 0 }) == 0;
                    };
                }
                close();
            } else {
                have to_integer(j) < to_integer(hi - 1) by {
                    apply(integer::int32_less_equal_and_not_equal_implies_less_than(j, hi - 1));
                    close();
                }
                apply(ih(hi - 1));
                have a[hi - 1] == b[hi - 1] by {
                    have j < (hi - 1) and (hi - 1) < n;
                    instantiate(forall (k: int32) {
                        j < k and k < n implies a[k] == b[k]
                    }, hi - 1);
                    close();
                }
                unfold(unmarked(a, lo, hi));
                unfold(unmarked(b, lo, hi));
                have to_integer(if a[hi - 1] == 0 { 1 } else { 0 })
                    == to_integer(if b[hi - 1] == 0 { 1 } else { 0 }) by {
                    close() using { a[hi - 1] == b[hi - 1]; };
                }
                have unmarked(b, lo, hi - 1)
                    + to_integer(if b[hi - 1] == 0 { 1 } else { 0 })
                    == unmarked(a, lo, hi - 1)
                        + to_integer(if a[hi - 1] == 0 { 1 } else { 0 }) - 1 by {
                    close() using {
                        unmarked(b, lo, hi - 1) == unmarked(a, lo, hi - 1) - 1;
                        to_integer(if a[hi - 1] == 0 { 1 } else { 0 })
                            == to_integer(if b[hi - 1] == 0 { 1 } else { 0 });
                    };
                }
                close();
            }
        }
    }
}
