# a quantified fact that is not an equality crosses a separated store

The bound on every `next[k]` holds at `before`, and the store writes the
separated `visited`. One `transport` from the fact at `before` restates it
at the current state.

```c filename=quantified_frame_carries_a_bound_fact_to_the_current_state.c
void mark(int32 *next, int32 *visited, int32 n, int32 cur) {
    visited[cur] = 1;
}
```

```click
verifying "quantified_frame_carries_a_bound_fact_to_the_current_state.c";

void mark(int32 *next, int32 *visited, int32 n, int32 cur) {
    requires 0 <= cur;
    requires cur < n;
    views next[0..n];
    owns visited[0..n];
    requires forall (k: int32) { 0 <= k and k < n implies 0 <= next[k] and next[k] < n };
    ensures forall (k: int32) { 0 <= k and k < n implies 0 <= next[k] and next[k] < n };
} by {
    mark before;
    have at(before, forall (k: int32) { 0 <= k and k < n implies 0 <= next[k] and next[k] < n }) by assumption();
    step();
    transport(
        at(before, forall (k: int32) { 0 <= k and k < n implies 0 <= next[k] and next[k] < n }),
        forall (k: int32) { 0 <= k and k < n implies 0 <= next[k] and next[k] < n }
    ) using {
        at(before, forall (k: int32) { 0 <= k and k < n implies 0 <= next[k] and next[k] < n });
    }
    execute();
    simp();
}
```

```expect
pass
```
