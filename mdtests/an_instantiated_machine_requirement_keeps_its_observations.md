# An instantiated machine requirement keeps its observations

`big`'s requirement `100u64 < a` is a native `uint64` comparison. At
`a = n - k` it is the native comparison of the wrapping difference, which a
comparison that does arithmetic would read as the Integer `100 < n - k`
([Integer specification arithmetic](../docs/reference/language/index.md#integer-specification-arithmetic)).
The refusal therefore spells the instantiation by its observations,
`to_integer(100u64) < to_integer((n - k))`, and the `have` it suggests states
the required fact: pasted before the `apply`, it discharges it
(`the_suggested_have_for_a_machine_requirement_discharges_it.md`).

```click
theorem big(a: uint64) {
    requires 100u64 < a;
    ensures true by { solve(); }
}

theorem wrapped(n: uint64, k: uint64) {
    requires n == 5u64;
    requires k == 30u64;
    ensures true by {
        apply(big(n - k));
        solve();
    }
}
```

```expect
fail: required exact fact for theorem `big` is unavailable: requirement 1 `to_integer(100u64) < to_integer((n - k))` instantiates to to_integer(100u64) < to_integer((n - k))
  this is a search miss, not a refusal; no available fact states the requirement, and the elided `apply` proves none; if it holds, state it first with `have to_integer(100u64) < to_integer((n - k)) by { ... }`
```
