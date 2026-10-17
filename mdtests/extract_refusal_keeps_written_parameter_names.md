# An `extract` refusal keeps the written parameter names

The requested inequality is an entire known fact, so `extract` correctly
refuses it. Its diagnostic must retain `m` and `i` from the citation.

```c filename=f.c
void mark_one(int32 a[], int32 n, int32 i, int32 m) {
    a[i] = 1;
}
```

```click
verifying "f.c";

void mark_one(int32 a[], int32 n, int32 i, int32 m) {
    requires 0 <= i;
    requires i < n;
    requires 0 <= m;
    requires m < n;
    requires m != i;
    requires n <= 1073741823;
    owns a[0..n];
    ensures a[m] == old(a[m]);
} by {
    mark entry;
    step();
    have m != i by {
        extract(m != i);
    }
    execute();
    simp();
}
```

```expect
fail: `extract` proposition is not a proper conjunct, a checked disjunction projection, a discharged implication consequent, or a field equality of an exact same-constructor equality: m != i
```
