# An unsigned predecessor at zero is larger

```click
theorem wrapped_predecessor(n: uint64) {
    requires n == 0u64;
    ensures n == n by {
        induct(n) as ih;
        apply(ih(n - 1u64));
        simp();
    }
}
```

```expect
fail: induction hypothesis `ih` could not prove premise
```
