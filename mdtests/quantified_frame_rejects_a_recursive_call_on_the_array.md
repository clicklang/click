# a recursive call is framed by its own write set, not by the caller facts

The recursive call owns `v[0..n - 1]` and may write every cell of it, and
the caller's own bounds on `n` say nothing about which. The quantified frame
of `v[k]` across the call is refused.

```c filename=quantified_frame_rejects_a_recursive_call_on_the_array.c
void zap(int32 *v, int32 n) {
    if (n <= 0) return;
    v[n - 1] = 0;
    zap(v, n - 1);
}
```

```click
verifying "quantified_frame_rejects_a_recursive_call_on_the_array.c";

void zap(int32 *v, int32 n) {
    decreases n;
    requires n <= 1000;
    owns v[0..n];
    ensures forall (k: int32) { 0 <= k and k < n - 1 implies v[k] == old(v[k]) };
} by {
    branch then {
        step();
        simp();
    } else {}
    step();
    have 0 <= n - 1 by { arithmetic() using { 0 < n; } }
    have n - 1 <= 1000 by { arithmetic() using { 0 < n; n <= 1000; } }
    mark before_call;
    step();
    transport(
        forall (k: int32) { 0 <= k and k < n - 1 implies at(before_call, v[k]) == at(before_call, v[k]) },
        forall (k: int32) { 0 <= k and k < n - 1 implies v[k] == at(before_call, v[k]) }
    ) using {
        forall (k: int32) { 0 <= k and k < n - 1 implies at(before_call, v[k]) == at(before_call, v[k]) };
    }
    execute();
    simp();
}
```

```expect
fail: quantified frame: a leaf was not carried
```
