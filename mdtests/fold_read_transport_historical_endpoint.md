# a fold whose endpoint is a historical read keeps that endpoint

The prefix ends at `m[0]` as read at entry. That argument is an evaluated
value, not an instruction to reload `m[0]` later, so both applications spell
the same endpoint `at(entry, m[0])`. The store writes `v[m[0]]` through the
same load, which is exactly the prefix's end.

```c filename=fold_read_transport_historical_endpoint.c
void mark_at(int32 *v, int32 *m, int32 n) {
    v[m[0]] = 1;
}
```

```click
verifying "fold_read_transport_historical_endpoint.c";

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
        let ih = induct(hi);
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


void mark_at(int32 *v, int32 *m, int32 n) {
    requires 0 <= m[0];
    requires m[0] < n;
    views m[0..1];
    owns v[0..n];
    requires separate(memory(v[0..n]), memory(m[0..1]));
} by {
    mark entry;
    have exists (end: int32) { end == at(entry, m[0]) } by {
        witness(at(entry, m[0]));
        known();
    }
    obtain (end: int32) { end == at(entry, m[0]) };
    have zeros(at(entry, v), 0, end) == zeros(at(entry, v), 0, end) by normalize();
    have 0 <= 0 by { normalize(); }
    have 0 <= end by { known(); }
    have end <= n by { solve(); }
    have viewable(v[0..n]) by { observe(v[0..n]); known(); }
    have contains(memory(v[0..n]), memory(v[0..end])) by {
        apply(click::separation::contains_subrange(v, 0, n, 0, end)) using { 0 <= 0; 0 <= end; end <= n; };
    }
    have viewable(v[0..end]) by {
        apply(click::separation::viewable_restrict(memory(v[0..n]), memory(v[0..end]))) using {
            viewable(v[0..n]); contains(memory(v[0..n]), memory(v[0..end]));
        };
    }
    have forall (k: int32) { 0 <= k and k < end implies separate(memory(v[m[0]]), memory(v[k])) } by {
        intro(); intro();
        have m[0] != k by { solve(); }
        apply(click::separation::separate_elements(v, m[0], k)) using { m[0] != k; };
    }
    have contains(memory(v[0..n]), memory(v[m[0]])) by {
        apply(click::separation::contains_element(v, 0, n, m[0])) using { 0 <= m[0]; m[0] < n; };
    }
    have contains(memory(m[0..1]), memory(m[0..1])) by {
        apply(click::separation::contains_refl(memory(m[0..1])));
    }
    have separate(memory(v[m[0]]), memory(m[0..1])) by {
        apply(click::separation::separate_restrict(memory(v[0..n]), memory(m[0..1]), memory(v[m[0]]), memory(m[0..1]))) using {
            separate(memory(v[0..n]), memory(m[0..1]));
            contains(memory(v[0..n]), memory(v[m[0]]));
            contains(memory(m[0..1]), memory(m[0..1]));
        };
    }
    step() by { known(); }
    have zeros(at(entry, v), 0, end) == zeros(v, 0, end) by {
        have forall (k: int32) { 0 <= k and k < end implies v[k] == at(entry, v[k]) } by {
            intro(); intro();
            instantiate(at(entry, forall (j: int32) { 0 <= j and j < end implies separate(memory(v[m[0]]), memory(v[j])) }), k);
            have separate(statement(0).footprint, memory(v[k])) by {
                normalize() using { at(entry, separate(memory(v[m[0]]), memory(v[k]))); };
            }
            preserve(memory(v[k]), statement(0));
        }
        have viewable(v[0..n]) by { observe(v[0..n]); known(); }
        have viewable(v[0..end]) by {
            apply(click::separation::viewable_restrict(memory(v[0..n]), memory(v[0..end]))) using {
                viewable(v[0..n]); contains(memory(v[0..n]), memory(v[0..end]));
            };
        }
        have end <= 1073741823 by { solve(); }
        apply(same_zeros(v, at(entry, v), 0, end, end)) using {
            0 <= 0; 0 <= end; end <= end;
            viewable(v[0..end]); at(entry, viewable(v[0..end]));
            forall (k: int32) { 0 <= k and k < end implies v[k] == at(entry, v[k]) };
        };
        known();
    }
}
```

```expect
pass
```
