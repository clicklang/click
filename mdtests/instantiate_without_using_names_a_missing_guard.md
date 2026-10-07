# instantiate without using names a missing guard

Without a list, `instantiate` only looks its guards up; it does not derive
them. Here `k < n` follows from `k < m` and `m == n` but is not itself a fact,
so the step is refused and names the guard. Listing those two facts with
`using`, or proving `k < n` first with `have`, repairs it.

```click
theorem bare_instantiate_missing_guard(n: int32, m: int32, k: int32) {
    requires forall (j: int32) { 0 <= j and j < n implies j + 0 == j };
    requires 0 <= k;
    requires k < m;
    requires m == n;
    ensures k + 0 == k by {
        instantiate(forall (j: int32) {
            0 <= j and j < n implies j + 0 == j
        }, k);
    }
}
```

```expect
fail: `instantiate` without `using` needs each instantiated guard as an exact fact, and `k < n is true` is not one
```
