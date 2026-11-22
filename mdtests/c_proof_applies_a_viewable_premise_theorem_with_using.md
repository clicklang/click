# Applying a theorem checks a readable range and its span

A C contract's stated range supplies its readability and the bounds that
make it a valid byte span. The theorem application checks both from those
facts in scope.

```c filename=c_proof_applies_a_loadable_premise_theorem_with_using.c
int32 probe(int32 a[], int32 n) {
    return 0;
}
```

```click
verifying "c_proof_applies_a_loadable_premise_theorem_with_using.c";

theorem viewable_range_is_nonnegative(v: int32[], n: int32) {
    requires n >= 0 and viewable(v[0..n]);
    ensures 0 <= n by solve();
}

int32 probe(int32 a[], int32 n) {
    requires 0 <= n;
    requires n <= 1073741823;
    requires viewable(a[0..n]);
    ensures result == 0;
} by {
    step();
    have n >= 0;
    have viewable(a[0..n]);
    have n >= 0 and viewable(a[0..n]) by known();
    apply(viewable_range_is_nonnegative(a, n));
    solve();
}
```

```expect
pass
```
