# A uint64 induction call must decrease

```click
theorem same_measure(n: uint64) {
    ensures n == n by {
        induct(n) as ih;
        apply(ih(n));
        simp();
    }
}
```

```expect
fail: induction hypothesis `ih` could not prove premise `n < n`
```
