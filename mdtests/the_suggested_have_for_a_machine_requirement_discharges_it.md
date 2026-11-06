# The suggested `have` for a machine requirement discharges it

The `have` that
`an_instantiated_machine_requirement_keeps_its_observations.md` suggests,
pasted before the `apply`, states the native requirement `100u64 < a` at
`a = n - k`: the wrapping difference, 18446744073709551591, exceeds 100.

```click
theorem big(a: uint64) {
    requires 100u64 < a;
    ensures true by { solve(); }
}

theorem wrapped(n: uint64, k: uint64) {
    requires n == 5u64;
    requires k == 30u64;
    ensures true by {
        have to_integer(100u64) < to_integer((n - k)) by { solve(); }
        apply(big(n - k));
        solve();
    }
}
```

```expect
pass
```
