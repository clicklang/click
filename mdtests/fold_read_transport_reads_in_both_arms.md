# repeated reads of the fold's cell in both arms are one support

`weighted` reads `v[k]` in its condition and in both arms. Every read is the
array at the fold's own binder, so the support is still `lo <= k < hi`, and
the store at the endpoint misses it.

```c filename=fold_read_transport_reads_in_both_arms.c
void set_end(int32 *v, int32 i, int32 n) {
    v[i] = 1;
}
```

```click
verifying "fold_read_transport_reads_in_both_arms.c";

function weighted(v: int32[], lo: int32, hi: int32) -> Integer {
    (lo..hi).fold(0, |acc, k| { acc + to_integer(if v[k] == 0 { v[k] } else { v[k] }) })
}

theorem same_weighted(p: int32[], q: int32[], lo: int32, n: int32, hi: int32) {
    requires 0 <= lo;
    requires 0 <= hi;
    requires hi <= n;
    requires viewable(p[0..n]);
    requires viewable(q[0..n]);
    requires forall (k: int32) { lo <= k and k < n implies p[k] == q[k] };
    ensures weighted(p, lo, hi) == weighted(q, lo, hi) by {
        let ih = induct(hi);
        if hi <= lo {
            unfold(weighted(p, lo, hi));
            unfold(weighted(q, lo, hi));
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
            unfold(weighted(p, lo, hi));
            unfold(weighted(q, lo, hi));
            rewrite(p[hi - 1], q[hi - 1]);
            known();
        }
    }
}


void set_end(int32 *v, int32 i, int32 n) {
    requires 0 <= i;
    requires i < n;
    owns v[0..n];
    ensures weighted(v, 0, i) == old(weighted(v, 0, i));
} by {
    mark entry;
    have weighted(at(entry, v), 0, i) == weighted(at(entry, v), 0, i) by known();
    have 0 <= 0 by { known(); }
    have 0 <= i by { known(); }
    have i <= n by { solve(); }
    have viewable(v[0..n]) by { observe(v[0..n]); known(); }
    have contains(memory(v[0..n]), memory(v[0..i])) by {
        apply(click::separation::contains_subrange(v, 0, n, 0, i));
    }
    have viewable(v[0..i]) by {
        apply(click::separation::viewable_restrict(memory(v[0..n]), memory(v[0..i])));
    }
    step();
    have weighted(at(entry, v), 0, i) == weighted(v, 0, i) by {
        have forall (k: int32) { 0 <= k and k < i implies v[k] == at(entry, v[k]) } by {
            intro(); intro();
            have i != k by { solve(); }
            have separate(memory(v[i]), memory(v[k])) by {
                apply(click::separation::separate_elements(v, i, k));
            }
            have separate(statement(0).footprint, memory(v[k])) by {
                solve() using { separate(memory(v[i]), memory(v[k])); };
            }
            preserve(memory(v[k]), statement(0));
        }
        have viewable(v[0..n]) by { observe(v[0..n]); known(); }
        have viewable(v[0..i]) by {
            apply(click::separation::viewable_restrict(memory(v[0..n]), memory(v[0..i])));
        }
        have i <= 1073741823 by { solve(); }
        apply(same_weighted(v, at(entry, v), 0, i, i));
        known();
    }
}
```

```expect
pass
```
