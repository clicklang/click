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
import "fold_read_transport_lemmas.click";
verifying "fold_read_transport_through_a_separated_alias.c";


void mark_other(int32 *a, int32 *b, int32 j, int32 n) {
    requires 0 <= j;
    requires j < n;
    views a[0..n];
    owns b[0..n];
    requires separate(memory(a[0..n]), memory(b[0..n]));
    ensures zeros(a, 0, n) == old(zeros(a, 0, n));
} by {
    mark entry;
    have zeros(at(entry, a), 0, n) == zeros(at(entry, a), 0, n) by known();
    have contains(memory(b[0..n]), memory(b[j])) by {
        apply(click::separation::contains_element(b, 0, n, j));
    }
    have contains(memory(a[0..n]), memory(a[0..n])) by {
        apply(click::separation::contains_refl(memory(a[0..n])));
    }
    have separate(memory(b[j]), memory(a[0..n])) by {
        apply(click::separation::separate_restrict(memory(b[0..n]), memory(a[0..n]), memory(b[j]), memory(a[0..n])));
    }
    have 0 <= 0 by { known(); }
    have 0 <= n by { solve(); }
    have viewable(a[0..n]) by { observe(a[0..n]); known(); }
    step();
    have zeros(at(entry, a), 0, n) == zeros(a, 0, n) by {
        have forall (k: int32) { 0 <= k and k < n implies a[k] == at(entry, a[k]) } by {
            intro(); intro();
            have contains(memory(a[0..n]), memory(a[k])) by {
                apply(click::separation::contains_element(a, 0, n, k));
            }
            have contains(memory(b[j]), memory(b[j])) by {
                apply(click::separation::contains_refl(memory(b[j])));
            }
            have separate(memory(b[j]), memory(a[k])) by {
                apply(click::separation::separate_restrict(memory(b[j]), memory(a[0..n]), memory(b[j]), memory(a[k])));
            }
            have separate(statement(0).footprint, memory(a[k])) by {
                solve() using { separate(memory(b[j]), memory(a[k])); };
            }
            preserve(memory(a[k]), statement(0));
        }
        have viewable(a[0..n]) by { observe(a[0..n]); known(); }
        apply(same_zeros(a, at(entry, a), 0, n, n));
        known();
    }
}
```

```expect
pass
```
