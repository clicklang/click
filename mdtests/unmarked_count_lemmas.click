import click::integer;
import click::machine_integer;

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
        induct(hi) as ih;
        if hi <= lo {
            peel(unmarked(v, lo, hi)) using { hi <= lo; };
            simp();
        } else {
            have 0 <= to_integer(hi - 1) by { arithmetic() using { 0 <= lo; lo < hi; }; }
            have to_integer(hi - 1) < to_integer(hi) by { arithmetic() using { 0 <= lo; lo < hi; }; }
            have to_integer(hi - 1) <= to_integer(n) by { arithmetic() using { 0 <= lo; lo < hi; hi <= n; }; }
            apply(ih(hi - 1)) using {
                0 <= to_integer(hi - 1);
                to_integer(hi - 1) < to_integer(hi);
                0 <= lo;
                to_integer(hi - 1) <= to_integer(n);
                n <= 1073741823;
                viewable(v[lo..n]);
            };
            have to_integer(lo) <= to_integer(hi - 1) by { arithmetic() using { 0 <= lo; lo < hi; }; }
            have to_integer(hi - 1) < 2147483647 by { arithmetic() using { 0 <= lo; lo < hi; }; }
            peel(unmarked(v, lo, hi)) using {
                to_integer(lo) <= to_integer(hi - 1);
                to_integer(hi - 1) < 2147483647;
            };
            have 0 <= (if v[hi - 1] == 0 { 1 } else { 0 });
            have to_integer(0) <= to_integer((if v[hi - 1] == 0 { 1 } else { 0 })) by auto();
            have 0 <= unmarked(v, lo, hi - 1)
                + to_integer(if v[hi - 1] == 0 { 1 } else { 0 }) by {
                arithmetic() using {
                    0 <= unmarked(v, lo, hi - 1);
                    to_integer(0) <= to_integer(if v[hi - 1] == 0 { 1 } else { 0 });
                };
            }
            assumption();
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
        induct(hi) as ih;
        if hi <= lo {
            peel(unmarked(a, lo, hi)) using { hi <= lo; };
            peel(unmarked(b, lo, hi)) using { hi <= lo; };
            simp();
        } else {
            have 0 <= to_integer(hi - 1) by { arithmetic() using { 0 <= lo; lo < hi; }; }
            have to_integer(hi - 1) < to_integer(hi) by { arithmetic() using { 0 <= lo; lo < hi; }; }
            have to_integer(lo) <= to_integer(hi - 1) by { arithmetic() using { 0 <= lo; lo < hi; }; }
            have to_integer(hi - 1) <= to_integer(m) by { arithmetic() using { 0 <= lo; lo < hi; hi <= m; }; }
            have to_integer(hi - 1) < to_integer(m) by { arithmetic() using { 0 <= lo; lo < hi; hi <= m; }; }
            have to_integer(hi - 1) < 2147483647 by { arithmetic() using { 0 <= lo; lo < hi; }; }
            apply(ih(hi - 1)) using {
                0 <= to_integer(hi - 1);
                to_integer(hi - 1) < to_integer(hi);
                0 <= lo;
                to_integer(hi - 1) <= to_integer(m);
                m <= n;
                n <= 1073741823;
                viewable(a[lo..n]);
                viewable(b[lo..n]);
                forall (k: int32) { lo <= k and k < m implies a[k] == b[k] };
            };
            have a[hi - 1] == b[hi - 1] by {
                instantiate(forall (k: int32) {
                    lo <= k and k < m implies a[k] == b[k]
                }, hi - 1) using { to_integer(lo) <= to_integer(hi - 1); to_integer(hi - 1) < to_integer(m); };
                assumption();
            }
            peel(unmarked(a, lo, hi)) using {
                to_integer(lo) <= to_integer(hi - 1);
                to_integer(hi - 1) < 2147483647;
            };
            peel(unmarked(b, lo, hi)) using {
                to_integer(lo) <= to_integer(hi - 1);
                to_integer(hi - 1) < 2147483647;
            };
            have to_integer(if a[hi - 1] == 0 { 1 } else { 0 })
                == to_integer(if b[hi - 1] == 0 { 1 } else { 0 }) by {
                simp() using { a[hi - 1] == b[hi - 1]; };
            }
            have unmarked(a, lo, hi - 1)
                + to_integer(if a[hi - 1] == 0 { 1 } else { 0 })
                == unmarked(b, lo, hi - 1)
                    + to_integer(if b[hi - 1] == 0 { 1 } else { 0 }) by {
                arithmetic() using {
                    unmarked(a, lo, hi - 1) == unmarked(b, lo, hi - 1);
                    to_integer(if a[hi - 1] == 0 { 1 } else { 0 })
                        == to_integer(if b[hi - 1] == 0 { 1 } else { 0 });
                };
            }
            assumption();
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
        induct(hi) as ih;
        if hi <= lo {
            have j < lo by { arithmetic() using { j < hi; hi <= lo; }; }
            contradiction(lo <= j);
        } else {
            have 0 <= to_integer(hi - 1) by { arithmetic() using { 0 <= lo; lo < hi; }; }
            have to_integer(hi - 1) < to_integer(hi) by { arithmetic() using { 0 <= lo; lo < hi; }; }
            have to_integer(lo) <= to_integer(hi - 1) by { arithmetic() using { 0 <= lo; lo < hi; }; }
            have to_integer(hi - 1) <= to_integer(n) by { arithmetic() using { 0 <= lo; lo < hi; hi <= n; }; }
            have to_integer(hi - 1) < to_integer(n) by { arithmetic() using { 0 <= lo; lo < hi; hi <= n; }; }
            have to_integer(hi - 1) < 2147483647 by { arithmetic() using { 0 <= lo; lo < hi; }; }
            have to_integer(j) <= to_integer(hi - 1) by { arithmetic() using { 0 <= lo; lo < hi; j < hi; }; }
            if to_integer(j) == to_integer(hi - 1) {
                have j <= n by { arithmetic() using { j < hi; hi <= n; }; }
                have to_integer(hi - 1) <= to_integer(j) by {
                    arithmetic() using { 0 <= lo; lo < hi; to_integer(j) == to_integer(hi - 1); };
                }
                apply(unmarked_frame(a, b, lo, n, j, hi - 1)) using {
                    0 <= lo;
                    0 <= to_integer(hi - 1);
                    to_integer(hi - 1) <= to_integer(j);
                    j <= n;
                    n <= 1073741823;
                    viewable(a[lo..n]);
                    viewable(b[lo..n]);
                    forall (k: int32) { lo <= k and k < j implies a[k] == b[k] };
                };
                have a[hi - 1] == 0 by { simp() using { a[j] == 0; to_integer(j) == to_integer(hi - 1); }; }
                have b[hi - 1] != 0 by { simp() using { b[j] != 0; to_integer(j) == to_integer(hi - 1); }; }
                peel(unmarked(a, lo, hi)) using {
                    to_integer(lo) <= to_integer(hi - 1);
                    to_integer(hi - 1) < 2147483647;
                };
                peel(unmarked(b, lo, hi)) using {
                    to_integer(lo) <= to_integer(hi - 1);
                    to_integer(hi - 1) < 2147483647;
                };
                have (if a[hi - 1] == 0 { 1 } else { 0 }) == 1 by {
                    normalize() using { a[hi - 1] == 0; };
                }
                have (if b[hi - 1] == 0 { 1 } else { 0 }) == 0 by {
                    normalize() using { b[hi - 1] != 0; };
                }
                have to_integer(if a[hi - 1] == 0 { 1 } else { 0 }) == 1 by {
                    simp() using { (if a[hi - 1] == 0 { 1 } else { 0 }) == 1; };
                }
                have to_integer(if b[hi - 1] == 0 { 1 } else { 0 }) == 0 by {
                    simp() using { (if b[hi - 1] == 0 { 1 } else { 0 }) == 0; };
                }
                have unmarked(b, lo, hi - 1)
                    + to_integer(if b[hi - 1] == 0 { 1 } else { 0 })
                    == unmarked(a, lo, hi - 1)
                        + to_integer(if a[hi - 1] == 0 { 1 } else { 0 }) - 1 by {
                    arithmetic() using {
                        unmarked(a, lo, hi - 1) == unmarked(b, lo, hi - 1);
                        to_integer(if a[hi - 1] == 0 { 1 } else { 0 }) == 1;
                        to_integer(if b[hi - 1] == 0 { 1 } else { 0 }) == 0;
                    };
                }
                assumption();
            } else {
                have to_integer(j) < to_integer(hi - 1) by {
                    apply(int32_less_equal_and_not_equal_implies_less_than(j, hi - 1)) using {
                        to_integer(j) <= to_integer(hi - 1);
                        to_integer(j) != to_integer(hi - 1);
                    };
                    assumption();
                }
                apply(ih(hi - 1)) using {
                    0 <= to_integer(hi - 1);
                    to_integer(hi - 1) < to_integer(hi);
                    0 <= lo;
                    to_integer(hi - 1) <= to_integer(n);
                    n <= 1073741823;
                    viewable(a[lo..n]);
                    viewable(b[lo..n]);
                    lo <= j;
                    to_integer(j) < to_integer(hi - 1);
                    a[j] == 0;
                    b[j] != 0;
                    forall (k: int32) { lo <= k and k < j implies a[k] == b[k] };
                    forall (k: int32) { j < k and k < n implies a[k] == b[k] };
                };
                have a[hi - 1] == b[hi - 1] by {
                    instantiate(forall (k: int32) {
                        j < k and k < n implies a[k] == b[k]
                    }, hi - 1) using { to_integer(j) < to_integer(hi - 1); to_integer(hi - 1) < to_integer(n); };
                    assumption();
                }
                peel(unmarked(a, lo, hi)) using {
                    to_integer(lo) <= to_integer(hi - 1);
                    to_integer(hi - 1) < 2147483647;
                };
                peel(unmarked(b, lo, hi)) using {
                    to_integer(lo) <= to_integer(hi - 1);
                    to_integer(hi - 1) < 2147483647;
                };
                have to_integer(if a[hi - 1] == 0 { 1 } else { 0 })
                    == to_integer(if b[hi - 1] == 0 { 1 } else { 0 }) by {
                    simp() using { a[hi - 1] == b[hi - 1]; };
                }
                have unmarked(b, lo, hi - 1)
                    + to_integer(if b[hi - 1] == 0 { 1 } else { 0 })
                    == unmarked(a, lo, hi - 1)
                        + to_integer(if a[hi - 1] == 0 { 1 } else { 0 }) - 1 by {
                    arithmetic() using {
                        unmarked(b, lo, hi - 1) == unmarked(a, lo, hi - 1) - 1;
                        to_integer(if a[hi - 1] == 0 { 1 } else { 0 })
                            == to_integer(if b[hi - 1] == 0 { 1 } else { 0 });
                    };
                }
                assumption();
            }
        }
    }
}
