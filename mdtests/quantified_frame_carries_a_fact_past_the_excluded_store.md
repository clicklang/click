# a quantified fact crosses a store its guard excludes

`k != i` excludes the one cell `v[i] = 1` writes, so every other entry
value survives the store. One `transport`, with no source to prove and no
`using` list, carries the whole quantified fact.

```c filename=quantified_frame_carries_a_fact_past_the_excluded_store.c
void mark(int32 *v, int32 n, int32 i) {
    v[i] = 1;
}
```

```click
verifying "quantified_frame_carries_a_fact_past_the_excluded_store.c";

void mark(int32 *v, int32 n, int32 i) {
    requires 0 <= i;
    requires i < n;
    owns v[0..n];
    ensures forall (k: int32) { 0 <= k and k < n and k != i implies v[k] == old(v[k]) };
} by {
    step();
    transport(
        forall (k: int32) { 0 <= k and k < n and k != i implies old(v[k]) == old(v[k]) },
        forall (k: int32) { 0 <= k and k < n and k != i implies v[k] == old(v[k]) }
    ) using {
        forall (k: int32) { 0 <= k and k < n and k != i implies old(v[k]) == old(v[k]) };
    }
    execute();
    simp();
}
```

```expect
pass
```
