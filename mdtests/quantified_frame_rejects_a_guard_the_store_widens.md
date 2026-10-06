# a quantified frame checks the guard it admits as well as the body

The store `v[i] = 0` can make the guard `v[k] == 0` hold at `k == i` where
it did not at entry, and nothing says `w[i] == 1`. The guard's own read is
framed in the opposite direction from the body's, and it is not unchanged, so
the transport is refused.

```c filename=quantified_frame_rejects_a_guard_the_store_widens.c
void clear(int32 *v, int32 *w, int32 n, int32 i) {
    v[i] = 0;
}
```

```click
verifying "quantified_frame_rejects_a_guard_the_store_widens.c";

void clear(int32 *v, int32 *w, int32 n, int32 i) {
    requires 0 <= i;
    requires i < n;
    owns v[0..n];
    views w[0..n];
    requires forall (k: int32) { 0 <= k and k < n and v[k] == 0 implies w[k] == 1 };
    ensures forall (k: int32) { 0 <= k and k < n and v[k] == 0 implies w[k] == 1 };
} by {
    have forall (k: int32) { 0 <= k and k < n and old(v[k]) == 0 implies old(w[k]) == 1 } by { assumption(); }
    step();
    transport(
        forall (k: int32) { 0 <= k and k < n and old(v[k]) == 0 implies old(w[k]) == 1 },
        forall (k: int32) { 0 <= k and k < n and v[k] == 0 implies w[k] == 1 }
    ) using {
        forall (k: int32) { 0 <= k and k < n and old(v[k]) == 0 implies old(w[k]) == 1 };
    }
    execute();
    simp();
}
```

```expect
fail: quantified frame: a leaf was not carried
```
