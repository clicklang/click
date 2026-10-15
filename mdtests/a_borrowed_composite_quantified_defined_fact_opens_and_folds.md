# A borrowed composite's quantified `defined` fact opens and folds

`valid(p, n)` views `p[0..n]` and states that every cell of that range is
defined. Its quantified `defined(p[k])` read lies inside the viewed range
under the guard `0 <= k and k < n`, so it depends on the same loan as the
view. `first` borrows the composite and opens it; `mark` holds only a borrowed
view and folds the composite to produce it.

```c filename=a_borrowed_composite_quantified_defined_fact_opens_and_folds.c
int first(int p[], int n) { return p[0]; }

void mark(int p[], int n) { }
```

```click
resource valid(p: int32*, n: int32) {
    views p[0..n];
    fact forall (k: int32) { 0 <= k and k < n implies defined(p[k]) };
}

verifying "a_borrowed_composite_quantified_defined_fact_opens_and_folds.c";

int32 first(int32 p[], int32 n) {
    requires 0 < n;
    views valid(p, n);
    ensures true;
} by {
    open(valid(p, n)) {
        execute();
    }
}

void mark(int32 p[], int32 n) {
    requires 0 < n;
    requires forall (k: int32) { 0 <= k and k < n implies defined(p[k]) };
    views p[0..n];
    produces valid(p, n);
} by {
    execute();
    fold(valid(p, n));
}
```

```expect
pass
```
