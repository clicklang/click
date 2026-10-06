# a store to a global is not framed away from a quantified array read

`v` may point at the global `g`, so `g[0] = 1` may write `v[0]`. The
quantified frame is refused.

```c filename=quantified_frame_rejects_a_global_that_may_be_the_array.c
int32 g[4];

void mark_global(int32 v[], int32 n) {
    g[0] = 1;
}
```

```click
verifying "quantified_frame_rejects_a_global_that_may_be_the_array.c";

void mark_global(int32 v[], int32 n) {
    requires 0 < n;
    requires n <= 4;
    owns g[0..1];
    ensures forall (k: int32) { 0 <= k and k < n implies v[k] == old(v[k]) };
} by {
    step();
    transport(
        forall (k: int32) { 0 <= k and k < n implies old(v[k]) == old(v[k]) },
        forall (k: int32) { 0 <= k and k < n implies v[k] == old(v[k]) }
    ) using {
        forall (k: int32) { 0 <= k and k < n implies old(v[k]) == old(v[k]) };
    }
    execute();
    simp();
}
```

```expect
fail: quantified frame: a leaf was not carried
```
