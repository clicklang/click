# An ordinary separation clause needs no extent text

Separation states disjointness without introducing extent bounds. The viewed
resource clauses independently supply the validity needed for the read.

```c filename=an_ordinary_separation_clause_needs_no_extent_text.c
int32 ordinary_separation(int32 a[], int32 b[], int32 n) {
    return b[0];
}
```

```click
verifying "an_ordinary_separation_clause_needs_no_extent_text.c";

int32 ordinary_separation(int32 a[], int32 b[], int32 n) {
    requires 0 <= n;
    requires separate(memory(a[0..n]), memory(b[0..1]));
    owns b[0..1];

    ensures result == b[0];
}
```

```expect
pass
```
