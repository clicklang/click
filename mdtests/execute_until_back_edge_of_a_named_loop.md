# Finish a named loop's preservation region

`loop(i).back_edge()` is `back_edge()` with its loop written out: inside the
preservation region of `loop(i)` it finishes the region's remaining steps,
and inside any other region it is refused.

```c filename=named_back_edge.c
int32 count(int32 n) {
    int32 i;
    i = 0;
    while (i < n) { i = i + 1; }
    return i;
}
```

```click
verifying "named_back_edge.c";
int32 count(int32 n) {
 requires 0 <= n and n <= 1000;
 ensures result == n;
} by {
 execute_until(loop(0));
 loop {
  decreases n-i;
  invariant 0 <= i and i <= n;
  preserve by { execute_until(loop(0).back_edge()); close_invariants(); }
 }
 execute(); solve();
}
```

```expect
pass
```
