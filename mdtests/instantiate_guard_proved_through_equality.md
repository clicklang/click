# Instantiation uses an ordinary guard proof through equality

`have k < n by known()` uses equality closure. Instantiation itself preserves
the guard, which exact propagation then discharges from this ordinary fact.

```click
function tag(x: int32) -> int32 { x }

theorem bare_instantiate_missing_guard(n: int32, m: int32, k: int32) {
    requires forall (j: int32) { 0 <= j and j < n implies tag(j) == 0 };
    requires 0 <= k;
    requires k < m;
    requires m == n;
    ensures tag(k) == 0 by {
        have k < n by known();
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
