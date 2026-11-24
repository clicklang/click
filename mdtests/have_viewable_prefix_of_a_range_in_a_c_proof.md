# `have viewable(...)` proves a prefix of a range in a C proof

The C proof preserves the view of `a[0..n]` across the return, then proves
that `a[0..k]` lies inside it. The separate footprint and the containment
facts give expansion the exact evidence for the smaller view. The nonnegative
bound on `n` follows from `0 <= k` and `k <= n`.

```c filename=have_loadable_prefix_of_a_range_in_a_c_proof.c
int32 probe(int32 a[], int32 n, int32 k) {
    return 0;
}
```

```click
verifying "have_loadable_prefix_of_a_range_in_a_c_proof.c";

int32 probe(int32 a[], int32 n, int32 k) {
    requires 0 <= k;
    requires k <= n;
    requires viewable(a[0..n]);
    ensures result == 0;
} by {
    step();
    apply(click::integer::int32_less_equal_transitive(0, k, n));
    have separate(statement(0).footprint, memory(a[0..n])) by { close(); }
    have viewable(a[0..n]) by {
        preserve(memory(a[0..n]), statement(0));
    }
    apply(click::separation::contains_subrange(a, 0, n, 0, k));
    have viewable(a[0..k]) by {
        apply(click::separation::viewable_restrict(memory(a[0..n]), memory(a[0..k])));
    }
    close();
}
```

```expect
pass
```
