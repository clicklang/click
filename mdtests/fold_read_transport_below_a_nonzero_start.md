# a store below a nonzero lower endpoint misses the fold

`zeros(v, lo, hi)` reads the cells `lo <= k < hi`. The store writes `v[j]`,
and `j < lo` places its four bytes below the first cell the fold reads. The
bound is an exact fact of the context; the frame rule looks it up and does
not search for it.

```c filename=fold_read_transport_below_a_nonzero_start.c
void mark_below(int32 *v, int32 lo, int32 hi, int32 j, int32 n) {
    v[j] = 1;
}
```

```click
verifying "fold_read_transport_below_a_nonzero_start.c";

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
            instantiate(forall (k: int32) { lo <= k and k < n implies p[k] == q[k] }, hi - 1) using {
                to_integer(lo) <= to_integer(hi - 1);
                to_integer(hi - 1) < to_integer(n);
            };
            have to_integer(lo) <= to_integer(hi - 1) by { solve(); }
            have to_integer(hi - 1) < 2147483647 by { solve(); }
            unfold(zeros(p, lo, hi));
            unfold(zeros(q, lo, hi));
            rewrite(p[hi - 1], q[hi - 1]);
            known();
        }
    }
}

void mark_below(int32 *v, int32 lo, int32 hi, int32 j, int32 n) {
    requires 0 <= j;
    requires j < lo;
    requires lo <= hi;
    requires hi <= n;
    owns v[0..n];
    ensures zeros(v, lo, hi) == old(zeros(v, lo, hi));
} by {
    mark entry;
    have zeros(at(entry, v), lo, hi) == zeros(at(entry, v), lo, hi) by normalize();
    have 0 <= lo by { solve(); }
    have 0 <= hi by { solve(); }
    have viewable(v[0..n]) by { observe(v[0..n]); known(); }
    step();
    have zeros(at(entry, v), lo, hi) == zeros(v, lo, hi) by {
        have forall (k: int32) { lo <= k and k < n implies v[k] == at(entry, v[k]) } by {
            intro(); intro();
            have 0 <= k by { solve(); }
            have j != k by { solve(); }
            have separate(memory(v[j]), memory(v[k])) by {
                apply(click::separation::separate_elements(v, j, k)) using { j != k; };
            }
            have separate(statement(0).footprint, memory(v[k])) by {
                normalize() using { separate(memory(v[j]), memory(v[k])); };
            }
            preserve(memory(v[k]), statement(0));
        }
        have viewable(v[0..n]) by { observe(v[0..n]); known(); }
        apply(same_zeros(v, at(entry, v), lo, n, hi)) using {
            0 <= lo;
            0 <= hi;
            hi <= n;
            viewable(v[0..n]);
            at(entry, viewable(v[0..n]));
            forall (k: int32) { lo <= k and k < n implies v[k] == at(entry, v[k]) };
        };
        known();
    }
}
```

```expect
pass
```
