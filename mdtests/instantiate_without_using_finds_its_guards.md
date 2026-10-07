# instantiate without using finds its guards

The guards of a universal fact at a value are fixed by the fact and the value,
so `instantiate` without a `using` list looks each one up as an exact fact
instead of asking for it to be retyped.

```click
theorem bare_instantiate(n: int32, k: int32) {
    requires forall (j: int32) { 0 <= j and j < n implies j + 0 == j };
    requires 0 <= k;
    requires k < n;
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
