# a viewed array crosses a store and a call into a separated one

`left[0..n]` is viewed and `visited[0..n]` owned, so the contract's entry
partition separates them. The store `visited[cur] = 1` and the call, whose
checked write set is `visited[0..n]`, both miss every `left[k]` the guard
admits, so the entry values of `left` carry across both, and `simp` finds
the transport.

```c filename=quantified_frame_carries_a_separated_array_past_a_store_and_a_call.c
void touch(int32 *visited, int32 n) {
    visited[0] = 2;
}

void walk(int32 *left, int32 *visited, int32 n, int32 cur) {
    visited[cur] = 1;
    touch(visited, n);
}
```

```click
verifying "quantified_frame_carries_a_separated_array_past_a_store_and_a_call.c";

void touch(int32 *visited, int32 n) {
    requires 0 < n;
    owns visited[0..n];
} by {
    execute();
    simp();
}

void walk(int32 *left, int32 *visited, int32 n, int32 cur) {
    requires 0 <= cur;
    requires cur < n;
    views left[0..n];
    owns visited[0..n];
    ensures forall (k: int32) { 0 <= k and k < n implies left[k] == old(left[k]) };
} by {
    step();
    step();
    have forall (k: int32) { 0 <= k and k < n implies left[k] == old(left[k]) };
    execute();
    simp();
}
```

```expect
pass
```
