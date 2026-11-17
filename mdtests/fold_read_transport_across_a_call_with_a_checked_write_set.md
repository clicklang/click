# a call whose write set starts at the fold's end is framed

`fill` owns `v[lo..n]`, so the call's checked write set is `v[i..n]`. With
`i <= n` that range is well formed and starts exactly where `zeros(v, 0, i)`
ends, so the application survives the call. The proof applies
`separate_adjacent_ranges`, restricts separation to the
call's recorded footprint and each selected cell, then uses `preserve` and
an ordinary induction lemma for the fold.

```c filename=fold_read_transport_across_a_call_with_a_checked_write_set.c
void fill(int32 *v, int32 lo, int32 n) {
    v[lo] = 1;
}

void caller(int32 *v, int32 i, int32 n) {
    fill(v, i, n);
}
```

```click
verifying "fold_read_transport_across_a_call_with_a_checked_write_set.c";

function zeros(v: int32[], lo: int32, hi: int32) -> Integer {
    (lo..hi).fold(0, |acc, k| { acc + to_integer(if v[k] == 0 { 1 } else { 0 }) })
}

theorem same_zeros(p: int32[], q: int32[], lo: int32, n: int32, hi: int32) {
    requires 0 <= lo;
    requires 0 <= hi;
    requires hi <= n;
    requires viewable(p[0..n]);
    requires viewable(q[0..n]);
    requires forall (k: int32) { lo <= k and k < n implies p[k] == q[k] };
    ensures zeros(p, lo, hi) == zeros(q, lo, hi) by {
        induct(hi) as ih;
        if hi <= lo {
            unfold(zeros(p, lo, hi));
            unfold(zeros(q, lo, hi));
            known();
        } else {
            have lo < hi;
            have 0 <= to_integer(hi - 1) by { solve(); }
            have to_integer(hi - 1) < to_integer(hi) by { solve(); }
            have to_integer(hi - 1) <= to_integer(n) by { solve(); }
            apply(ih(hi - 1)) using {
                0 <= to_integer(hi - 1);
                to_integer(hi - 1) < to_integer(hi);
                0 <= lo;
                to_integer(hi - 1) <= to_integer(n);
                viewable(p[0..n]);
                viewable(q[0..n]);
                forall (k: int32) { lo <= k and k < n implies p[k] == q[k] };
            };
            have to_integer(hi - 1) < to_integer(n) by { solve(); }
            have to_integer(lo) <= to_integer(hi - 1) by { solve(); }
            have lo <= (hi - 1) and (hi - 1) < n;
            instantiate(forall (k: int32) { lo <= k and k < n implies p[k] == q[k] }, hi - 1);
            have to_integer(lo) <= to_integer(hi - 1) by { solve(); }
            have to_integer(hi - 1) < 2147483647 by { solve(); }
            unfold(zeros(p, lo, hi));
            unfold(zeros(q, lo, hi));
            rewrite(p[hi - 1], q[hi - 1]);
            known();
        }
    }
}

void fill(int32 *v, int32 lo, int32 n) {
    requires 0 <= lo;
    requires lo < n;
    owns v[lo..n];
}

void caller(int32 *v, int32 i, int32 n) {
    requires 0 <= i;
    requires i < n;
    owns v[0..n];
    ensures zeros(v, 0, i) == old(zeros(v, 0, i));
} by {
    mark entry;
    have zeros(at(entry, v), 0, i) == zeros(at(entry, v), 0, i) by normalize();
    have i <= n by { solve() using { i < n; }; }
    have 0 <= 0 by { normalize(); }
    have viewable(v[0..n]) by { observe(v[0..n]); known(); }
    have contains(memory(v[0..n]), memory(v[0..i])) by {
        apply(click::separation::contains_subrange(v, 0, n, 0, i)) using { 0 <= 0; 0 <= i; i <= n; };
    }
    have viewable(v[0..i]) by {
        apply(click::separation::viewable_restrict(memory(v[0..n]), memory(v[0..i]))) using {
            viewable(v[0..n]); contains(memory(v[0..n]), memory(v[0..i]));
        };
    }
    have 0 <= to_integer(n - i) by { solve(); }
    have to_integer(n - i) <= 1073741823 by { solve(); }
    step();
    have zeros(v, 0, i) == zeros(at(entry, v), 0, i) by {
        have forall (k: int32) { 0 <= k and k < i implies v[k] == at(entry, v[k]) } by {
            intro(); intro();
            have separate(memory(v[0..i]), memory(v[i..n])) by {
                apply(click::separation::separate_adjacent_ranges(v, 0, i, n)) using { 0 <= i; i <= n; };
            }
            have separate(memory(v[i..n]), memory(v[0..i])) by {
                apply(click::separation::separate_symm(memory(v[0..i]), memory(v[i..n]))) using {
                    separate(memory(v[0..i]), memory(v[i..n]));
                };
            }
            have contains(memory(v[0..i]), memory(v[k])) by {
                apply(click::separation::contains_element(v, 0, i, k)) using { 0 <= k; k < i; };
            }
            have contains(memory(v[i..n]), memory(v[i..n])) by {
                apply(click::separation::contains_refl(memory(v[i..n])));
            }
            have separate(memory(v[i..n]), memory(v[k])) by {
                apply(click::separation::separate_restrict(memory(v[i..n]), memory(v[0..i]), memory(v[i..n]), memory(v[k]))) using {
                    separate(memory(v[i..n]), memory(v[0..i]));
                    contains(memory(v[i..n]), memory(v[i..n]));
                    contains(memory(v[0..i]), memory(v[k]));
                };
            }
            have contains(memory(v[k]), memory(v[k])) by {
                apply(click::separation::contains_refl(memory(v[k])));
            }
            have separate(statement(0).footprint, memory(v[k])) by {
                apply(click::separation::separate_restrict(memory(v[i..n]), memory(v[k]), statement(0).footprint, memory(v[k]))) using {
                    separate(memory(v[i..n]), memory(v[k]));
                    contains(memory(v[i..n]), statement(0).footprint);
                    contains(memory(v[k]), memory(v[k]));
                };
            }
            preserve(memory(v[k]), statement(0));
        }
        have viewable(v[0..i]) by { observe(v[0..i]); known(); }
        have i <= 1073741823 by { solve(); }
        apply(same_zeros(v, at(entry, v), 0, i, i)) using {
            0 <= 0; 0 <= i; i <= i;
            viewable(v[0..i]); at(entry, viewable(v[0..i]));
            forall (k: int32) { 0 <= k and k < i implies v[k] == at(entry, v[k]) };
        };
        known();
    }
}
```

```expect
pass
```
