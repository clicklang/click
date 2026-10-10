# a separated range does not frame reads beyond it

The contract separates `left[0..n]` from `visited[0..n]`, and nothing
about `left[n]`. A caller may pass `visited == left + n`, and then
`visited[cur] = 1` with `cur == 0` writes `left[n]`, which the guard
`k < m` admits whenever `n < m`. The quantified fact is refused.

```c filename=quantified_frame_rejects_a_read_past_the_separated_range.c
void mark(int32 *left, int32 *visited, int32 n, int32 m, int32 cur) {
    visited[cur] = 1;
}
```

```click
verifying "quantified_frame_rejects_a_read_past_the_separated_range.c";

void mark(int32 *left, int32 *visited, int32 n, int32 m, int32 cur) {
    requires 0 <= cur;
    requires cur < n;
    requires n < m;
    owns visited[0..n];
    requires separate(memory(left[0..n]), memory(visited[0..n]));
    ensures forall (k: int32) { 0 <= k and k < m implies left[k] == old(left[k]) };
} by {
    step();
    have forall (k: int32) { 0 <= k and k < m implies left[k] == old(left[k]) };
    execute();
    simp();
}
```

```expect
fail: `simp` failed
```
