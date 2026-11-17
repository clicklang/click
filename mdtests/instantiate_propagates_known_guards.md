# Instantiation exposes a body whose guards are already known

The substituted implication is admitted intact. Exact proposition propagation
uses the already established guards to expose its conclusion.

```click
function tag(x: int32) -> int32 { x }

theorem bare_instantiate(n: int32, k: int32) {
    requires forall (j: int32) { 0 <= j and j < n implies tag(j) == 0 };
    requires 0 <= k;
    requires k < n;
    ensures tag(k) == 0 by {
        instantiate(forall (j: int32) {
            0 <= j and j < n implies tag(j) == 0
        }, k);
        known();
    }
}
```

```expect
pass
```
