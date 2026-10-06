# a quantified transport reaches a mark after a call, as the per-index one does

`left[0..n]` is viewed and `visited[0..n]` owned, so the store
`visited[cur] = 1` and the call writing `visited[0..n]` miss every `left[k]`
the guard admits. The explicit quantified `transport` carries the entry
values of `left` to the mark `after` set once the call returned.

The same step written per index (`intro`, then `transport` of
`old(left[k]) == old(left[k])`, then `assumption`) was accepted while this
quantified form was refused (the shape of the DFS in
`branching_graph_dfs.md`, whose right call needed the per-index form). A
load under the binder is lowered once, as a load variable whose snapshot is
the canonical projection of the snapshot it read, recorded for that one
address. Renaming the binder rewrote the address but kept the projected
snapshot, for which no projection of the new address was recorded, so the
history walk had no step to cross back to the call. The per-index form
lowered the read for the introduced `k` directly and recorded its
projection. Substitution through a load variable now re-projects from the
source snapshot, so both forms ask the history the same question.

The attacks on the same frame (a call writing the range, a recursive call
on the array, an unseparated alias) are the
`quantified_frame_rejects_*.md` family.

```c filename=quantified_frame_carries_a_viewed_array_to_a_mark_after_a_call.c
void touch(int32 *visited, int32 n, int32 at) {
    visited[at] = 2;
}

void walk(int32 *left, int32 *visited, int32 n, int32 cur) {
    visited[cur] = 1;
    touch(visited, n, left[cur]);
}
```

```click
verifying "quantified_frame_carries_a_viewed_array_to_a_mark_after_a_call.c";

void touch(int32 *visited, int32 n, int32 at) {
    requires 0 <= at;
    requires at < n;
    owns visited[0..n];
} by {
    execute();
    simp();
}

void walk(int32 *left, int32 *visited, int32 n, int32 cur) {
    requires 0 <= cur;
    requires cur < n;
    views left[0..n];
    requires forall (k: int32) { 0 <= k and k < n implies 0 <= left[k] and left[k] < n };
    owns visited[0..n];
    requires separate(memory(left[0..n]), memory(visited[0..n]));
} by {
    have 0 <= left[cur] and left[cur] < n by {
        instantiate(forall (k: int32) { 0 <= k and k < n implies 0 <= left[k] and left[k] < n }, cur) using { 0 <= cur; cur < n; }
        assumption();
    }
    step();
    mark after_mark;
    transport(
        forall (k: int32) { 0 <= k and k < n implies old(left[k]) == old(left[k]) },
        forall (k: int32) { 0 <= k and k < n implies old(left[k]) == at(after_mark, left[k]) }
    ) using { forall (k: int32) { 0 <= k and k < n implies old(left[k]) == old(left[k]) }; }
    step();
    mark after;
    transport(
        forall (k: int32) { 0 <= k and k < n implies old(left[k]) == old(left[k]) },
        forall (k: int32) { 0 <= k and k < n implies old(left[k]) == at(after, left[k]) }
    ) using { forall (k: int32) { 0 <= k and k < n implies old(left[k]) == old(left[k]) }; }
    execute();
    simp();
}
```

```expect
pass
```
