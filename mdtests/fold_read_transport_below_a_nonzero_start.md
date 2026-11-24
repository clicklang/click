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
import "fold_read_transport_lemmas.click";
verifying "fold_read_transport_below_a_nonzero_start.c";

void mark_below(int32 *v, int32 lo, int32 hi, int32 j, int32 n) {
    requires 0 <= j;
    requires j < lo;
    requires lo <= hi;
    requires hi <= n;
    owns v[0..n];
    ensures zeros(v, lo, hi) == old(zeros(v, lo, hi));
} by {
    mark entry;
    have zeros(at(entry, v), lo, hi) == zeros(at(entry, v), lo, hi) by close();
    have 0 <= lo by { close(); }
    have 0 <= hi by { close(); }
    have viewable(v[0..n]) by { observe(v[0..n]); close(); }
    step();
    have zeros(at(entry, v), lo, hi) == zeros(v, lo, hi) by {
        have forall (k: int32) { lo <= k and k < n implies v[k] == at(entry, v[k]) } by {
            intro(); intro();
            have 0 <= k by { close(); }
            have j != k by { close(); }
            have separate(memory(v[j]), memory(v[k])) by {
                apply(click::separation::separate_elements(v, j, k));
            }
            have separate(statement(0).footprint, memory(v[k])) by {
                close() using { separate(memory(v[j]), memory(v[k])); };
            }
            preserve(memory(v[k]), statement(0));
        }
        have viewable(v[0..n]) by { observe(v[0..n]); close(); }
        apply(same_zeros(v, at(entry, v), lo, n, hi));
        close();
    }
}
```

```expect
pass
```
