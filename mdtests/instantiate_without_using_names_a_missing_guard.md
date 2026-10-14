# Instantiate checks guards through equality closure

The guard `k < n` is available through `k < m` and `m == n`. Instantiation
uses that shared semantic lookup without unfolding or theorem search.

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
pass
```
