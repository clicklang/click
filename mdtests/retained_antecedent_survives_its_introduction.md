# An antecedent cannot introduce a division by zero as a fact

The quantified antecedent evaluates `n / k` when `k == 0`. Retaining an
antecedent must not turn its undefined evaluation into an assumption. The
original four-introduction script relied on hidden lowering guards; with
separate mandatory obligations, its unchanged claim is rejected.

```c filename=retained_antecedent_survives_its_introduction.c
int32 retained_antecedent(int32 n) {
    return n;
}
```

```click
verifying "retained_antecedent_survives_its_introduction.c";

int32 retained_antecedent(int32 n) {
    ensures result == n;
} by {
    step();
    have forall (k: int32) { k == 0 and n / k == n implies n == n } by {
        intro();
        intro();
        intro();
        intro();
        extract(n / k == n);
        normalize();
    }
    solve();
}
```

```expect
fail: not established: `forall
```
