# A quantified uint64 equality crosses a separated store

The structural frame route previously skipped 64-bit equality even when its
read-history checker could prove the complete eight-byte load unchanged. This
exercises the same missing condition case as the rbtree parent-word frame.

```c filename=probe.c
void mark(unsigned long *values, int32 *visited, int32 n, int32 cur, unsigned long stamp) {
    visited[cur] = 1;
}
```

```click
verifying "probe.c";
void mark(uint64 *values, int32 *visited, int32 n, int32 cur, uint64 stamp) {
    requires 0 <= cur;
    requires cur < n;
    views values[0..n];
    owns visited[0..n];
    requires forall (k: int32) { 0 <= k and k < n implies values[k] == stamp };
    ensures forall (k: int32) { 0 <= k and k < n implies values[k] == stamp };
} by {
    mark before;
    have at(before, forall (k: int32) { 0 <= k and k < n implies values[k] == stamp }) by assumption();
    have contains(memory(visited[0..n]), memory(visited[cur])) by {
        apply(click::separation::contains_element(visited, 0, n, cur)) using { 0 <= cur; cur < n; };
    }
    have contains(memory(values[0..n]), memory(values[0..n])) by {
        apply(click::separation::contains_refl(memory(values[0..n])));
    }
    have separate(memory(visited[cur]), memory(values[0..n])) by {
        apply(click::separation::restrict(memory(visited[0..n]), memory(values[0..n]), memory(visited[cur]), memory(values[0..n]))) using {
            separate(memory(visited[0..n]), memory(values[0..n]));
            contains(memory(visited[0..n]), memory(visited[cur]));
            contains(memory(values[0..n]), memory(values[0..n]));
        };
    }
    step();
    transport(
        at(before, forall (k: int32) { 0 <= k and k < n implies values[k] == stamp }),
        forall (k: int32) { 0 <= k and k < n implies values[k] == stamp }
    ) using {
        at(before, forall (k: int32) { 0 <= k and k < n implies values[k] == stamp });
    };
}
```

```expect
pass
```
