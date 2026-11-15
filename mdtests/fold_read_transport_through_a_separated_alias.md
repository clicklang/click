# a store through a separated array misses the fold

`a` and `b` are two `int32*` parameters, so they share the external-argument
object and no offset relates them. The stated `separate(...)` holds them
apart; the frame rule checks that the fold's cells lie inside its first range
and the written cell inside its second, from exact order facts.

```c filename=fold_read_transport_through_a_separated_alias.c
void mark_other(int32 *a, int32 *b, int32 j, int32 n) {
    b[j] = 1;
}
```

```click
verifying "fold_read_transport_through_a_separated_alias.c";

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
            peel(zeros(p, lo, hi)) using { hi <= lo; };
            peel(zeros(q, lo, hi)) using { hi <= lo; };
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
            instantiate(forall (k: int32) { lo <= k and k < n implies p[k] == q[k] }, hi - 1) using {
                to_integer(lo) <= to_integer(hi - 1);
                to_integer(hi - 1) < to_integer(n);
            };
            have to_integer(lo) <= to_integer(hi - 1) by { solve(); }
            have to_integer(hi - 1) < 2147483647 by { solve(); }
            peel(zeros(p, lo, hi)) using { to_integer(lo) <= to_integer(hi - 1); to_integer(hi - 1) < 2147483647; };
            peel(zeros(q, lo, hi)) using { to_integer(lo) <= to_integer(hi - 1); to_integer(hi - 1) < 2147483647; };
            rewrite(p[hi - 1], q[hi - 1]);
            known();
        }
    }
}


void mark_other(int32 *a, int32 *b, int32 j, int32 n) {
    requires 0 <= j;
    requires j < n;
    views a[0..n];
    owns b[0..n];
    requires separate(memory(a[0..n]), memory(b[0..n]));
    ensures zeros(a, 0, n) == old(zeros(a, 0, n));
} by {
    mark entry;
    have zeros(at(entry, a), 0, n) == zeros(at(entry, a), 0, n) by normalize();
    have contains(memory(b[0..n]), memory(b[j])) by {
        apply(click::separation::contains_element(b, 0, n, j)) using { 0 <= j; j < n; };
    }
    have contains(memory(a[0..n]), memory(a[0..n])) by {
        apply(click::separation::contains_refl(memory(a[0..n])));
    }
    have separate(memory(b[j]), memory(a[0..n])) by {
        apply(click::separation::separate_restrict(memory(b[0..n]), memory(a[0..n]), memory(b[j]), memory(a[0..n]))) using {
            separate(memory(b[0..n]), memory(a[0..n]));
            contains(memory(b[0..n]), memory(b[j]));
            contains(memory(a[0..n]), memory(a[0..n]));
        };
    }
    have 0 <= 0 by { normalize(); }
    have 0 <= n by { solve(); }
    have viewable(a[0..n]) by { observe(a[0..n]); known(); }
    step();
    have zeros(at(entry, a), 0, n) == zeros(a, 0, n) by {
        have forall (k: int32) { 0 <= k and k < n implies a[k] == at(entry, a[k]) } by {
            intro(); intro();
            have contains(memory(a[0..n]), memory(a[k])) by {
                apply(click::separation::contains_element(a, 0, n, k)) using { 0 <= k; k < n; };
            }
            have contains(memory(b[j]), memory(b[j])) by {
                apply(click::separation::contains_refl(memory(b[j])));
            }
            have separate(memory(b[j]), memory(a[k])) by {
                apply(click::separation::separate_restrict(memory(b[j]), memory(a[0..n]), memory(b[j]), memory(a[k]))) using {
                    separate(memory(b[j]), memory(a[0..n]));
                    contains(memory(b[j]), memory(b[j]));
                    contains(memory(a[0..n]), memory(a[k]));
                };
            }
            have separate(statement(0).footprint, memory(a[k])) by {
                normalize() using { separate(memory(b[j]), memory(a[k])); };
            }
            preserve(memory(a[k]), statement(0));
        }
        have viewable(a[0..n]) by { observe(a[0..n]); known(); }
        apply(same_zeros(a, at(entry, a), 0, n, n)) using {
            0 <= 0; 0 <= n; n <= n;
            viewable(a[0..n]); at(entry, viewable(a[0..n]));
            forall (k: int32) { 0 <= k and k < n implies a[k] == at(entry, a[k]) };
        };
        known();
    }
}
```

```expect
pass
```
