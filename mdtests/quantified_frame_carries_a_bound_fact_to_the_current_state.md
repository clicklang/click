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
    have contains(memory(visited[0..n]), memory(visited[cur])) by {
        apply(click::separation::contains_element(visited, 0, n, cur)) using { 0 <= cur; cur < n; };
    }
    have contains(memory(next[0..n]), memory(next[0..n])) by {
        apply(click::separation::contains_refl(memory(next[0..n])));
    }
    have separate(memory(visited[cur]), memory(next[0..n])) by {
        apply(click::separation::restrict(memory(visited[0..n]), memory(next[0..n]), memory(visited[cur]), memory(next[0..n]))) using {
            separate(memory(visited[0..n]), memory(next[0..n]));
            contains(memory(visited[0..n]), memory(visited[cur]));
            contains(memory(next[0..n]), memory(next[0..n]));
        };
    }
    step();
    transport(
        at(before, forall (k: int32) { 0 <= k and k < n implies 0 <= next[k] and next[k] < n }),
        forall (k: int32) { 0 <= k and k < n implies 0 <= next[k] and next[k] < n }
    ) using {
        at(before, forall (k: int32) { 0 <= k and k < n implies 0 <= next[k] and next[k] < n });
    };
}
```

```expect
pass
```
