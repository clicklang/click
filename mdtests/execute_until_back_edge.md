# Finish a loop preservation region

`back_edge()` checks the remaining steps of the current preservation region.
It rejects early exits and leaves invariant and decreasing-measure checks to
`close_invariants()`. It does not split branches.

```c filename=count.c
int32 count(int32 n) {
    int32 i;
    i = 0;
    while (i < n) { i = i + 1; }
    return i;
}
```

```click
verifying "count.c";
int32 count(int32 n) {
 requires 0 <= n and n <= 1000;
 ensures result == n;
} by {
 execute_until(loop(0));
 loop {
  decreases n-i;
  invariant 0 <= i and i <= n;
  preserve by { execute_until(back_edge()); close_invariants(); }
 }
 execute(); simp();
}
```

```expect
pass
```
