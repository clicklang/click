# Appending a nonzero element leaves the zero count unchanged

The endpoint store preserves each read in the `0..i` prefix. Induction
preserves the prefix count, and unfolding at `i + 1` shows that the
new element contributes zero.

```c filename=fold_read_solve_extends_endpoint_with_zero_contribution.c
void set_end(int32 *v, int32 i, int32 n) {
    v[i] = 1;
}
```

```click
verifying "fold_read_solve_extends_endpoint_with_zero_contribution.c";

function zeros(v: int32[], lo: int32, hi: int32) -> Integer {
    (lo..hi).fold(0, |acc, k| { acc + to_integer(if v[k] == 0 { 1 } else { 0 }) })
}

theorem zeros_frame(
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
    views a[lo..n];
    views b[lo..n];
    requires forall (k: int32) {
        lo <= k and k < m implies a[k] == b[k]
    };
    ensures zeros(a, lo, hi) == zeros(b, lo, hi) by {
        let ih = induct(hi);
        if hi <= lo {
            unfold(zeros(a, lo, hi));
            unfold(zeros(b, lo, hi));
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
            unfold(zeros(a, lo, hi));
            unfold(zeros(b, lo, hi));
            have to_integer(if a[hi - 1] == 0 { 1 } else { 0 })
                == to_integer(if b[hi - 1] == 0 { 1 } else { 0 }) by {
                rewrite(b[hi - 1], a[hi - 1]);
                close();
            }
            have zeros(a, lo, hi - 1)
                + to_integer(if a[hi - 1] == 0 { 1 } else { 0 })
                == zeros(b, lo, hi - 1)
                    + to_integer(if b[hi - 1] == 0 { 1 } else { 0 }) by {
                rewrite(zeros(a, lo, hi - 1), zeros(b, lo, hi - 1));
                rewrite(to_integer(if a[hi - 1] == 0 { 1 } else { 0 }),
                        to_integer(if b[hi - 1] == 0 { 1 } else { 0 }));
                close();
            }
            close();
        }
    }
}

void set_end(int32 *v, int32 i, int32 n) {
    requires 0 <= i;
    requires i < n;
    owns v[0..n];
    ensures zeros(v, 0, i + 1) == old(zeros(v, 0, i));
} by {
    mark entry;
    step();
    have forall (k: int32) {
        0 <= k and k < i implies v[k] == at(entry, v[k])
    } by {
        intro() {
            intro() {
                have k < n by { close() using { k < i; i < n; }; }
                have i != k by { close() using { k < i; }; }
                have separate(memory(v[i]), memory(v[k])) by {
                    apply(click::separation::separate_elements(v, i, k));
                }
                have separate(statement(0).footprint, memory(v[k])) by {
                    close() using { separate(memory(v[i]), memory(v[k])); };
                }
                preserve(memory(v[k]), statement(0));
            }
        }
    }
    have viewable(v[0..n]) by { observe(v[0..n]); close(); }
    have 0 <= 0 by { close(); }
    have i <= i by { close(); }
    apply(zeros_frame(v, at(entry, v), 0, n, i, i));
    have zeros(v, 0, i + 1) == zeros(v, 0, i) by {
        unfold(zeros(v, 0, i + 1));
        close();
    }
}
```

```expect
pass
```
