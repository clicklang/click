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
import "fold_read_transport_lemmas.click";
verifying "fold_read_transport_historical_endpoint.c";


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
        close();
    }
    let end = obtain(exists (end: int32) { end == at(entry, m[0]) });
    have zeros(at(entry, v), 0, end) == zeros(at(entry, v), 0, end) by close();
    have 0 <= 0 by { close(); }
    have 0 <= end by { close(); }
    have end <= n by { close(); }
    have viewable(v[0..n]) by { observe(v[0..n]); close(); }
    have contains(memory(v[0..n]), memory(v[0..end])) by {
        apply(click::separation::contains_subrange(v, 0, n, 0, end));
    }
    have viewable(v[0..end]) by {
        apply(click::separation::viewable_restrict(memory(v[0..n]), memory(v[0..end])));
    }
    have forall (k: int32) { 0 <= k and k < end implies separate(memory(v[m[0]]), memory(v[k])) } by {
        intro(); intro();
        have m[0] != k by { close(); }
        apply(click::separation::separate_elements(v, m[0], k));
    }
    have contains(memory(v[0..n]), memory(v[m[0]])) by {
        apply(click::separation::contains_element(v, 0, n, m[0]));
    }
    have contains(memory(m[0..1]), memory(m[0..1])) by {
        apply(click::separation::contains_refl(memory(m[0..1])));
    }
    have separate(memory(v[m[0]]), memory(m[0..1])) by {
        apply(click::separation::separate_restrict(memory(v[0..n]), memory(m[0..1]), memory(v[m[0]]), memory(m[0..1])));
    }
    step() by { close(); }
    have zeros(at(entry, v), 0, end) == zeros(v, 0, end) by {
        have forall (k: int32) { 0 <= k and k < end implies v[k] == at(entry, v[k]) } by {
            intro(); intro();
            instantiate(at(entry, forall (j: int32) { 0 <= j and j < end implies separate(memory(v[m[0]]), memory(v[j])) }), k);
            have separate(statement(0).footprint, memory(v[k])) by {
                close() using { at(entry, separate(memory(v[m[0]]), memory(v[k]))); };
            }
            preserve(memory(v[k]), statement(0));
        }
        have viewable(v[0..n]) by { observe(v[0..n]); close(); }
        have viewable(v[0..end]) by {
            apply(click::separation::viewable_restrict(memory(v[0..n]), memory(v[0..end])));
        }
        have end <= 1073741823 by { close(); }
        apply(same_zeros(v, at(entry, v), 0, end, end));
        close();
    }
}
```

```expect
pass
```
