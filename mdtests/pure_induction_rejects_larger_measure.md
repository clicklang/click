# a larger induction argument is rejected

The argument `n + 1` is defined here, so the premise the hypothesis cannot
prove is the decrease itself.

```click
theorem bad_larger(n: int32) {
    requires n >= 0;
    requires n <= 100;
    ensures n == n by {
        induct(n) as ih;
        apply(ih(n + 1));
        simp();
    }
}
```

```expect
fail: induction hypothesis `ih` could not prove premise `to_integer((n + 1)) < to_integer(n)`
```
