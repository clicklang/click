# an induction hypothesis requires a strictly smaller argument

```click
theorem bad_same(n: int32) {
    requires n >= 0;
    ensures n == n by {
        induct(n) as ih;
        apply(ih(n));
        simp();
    }
}
```

```expect
fail: induction hypothesis `ih` found no available fact for premise `n < n`
  this is a search miss, not a refusal; no available fact states the requirement, and the elided `apply` proves none; if it holds, state it first with `have n < n by { ... }`
```
