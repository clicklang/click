# A named back edge must be the preserved loop's

`loop(i).back_edge()` names the back edge of `loop(i)` only. This function
has one loop, so inside its preservation region `loop(1).back_edge()` is
refused, and the refusal names the loop being preserved.

```c filename=other_back_edge.c
int32 count(int32 n) {
    int32 i;
    i = 0;
    while (i < n) { i = i + 1; }
    return i;
}
```

```click
verifying "other_back_edge.c";
int32 count(int32 n) {
 requires 0 <= n and n <= 1000;
 ensures result == n;
} by {
 execute_until(loop(0));
 loop {
  decreases n-i;
  invariant 0 <= i and i <= n;
  preserve by { execute_until(loop(1).back_edge()); close_invariants(); }
 }
 execute(); simp();
}
```

```expect
fail: `loop(1).back_edge()` names the back edge of the `loop(1)` preservation region; this preservation region is `loop(0)`'s
```
