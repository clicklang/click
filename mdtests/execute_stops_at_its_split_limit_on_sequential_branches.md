# The implicit tail stops at its split limit on sequential branches

The implicit tail runs each arm of a C `if` to function exit, so a function of
`n` sequential branches gives it `2^n` paths. Past 1,024 splits it stops and
names the explicit join, instead of running until its step budget: eleven
branches split 2,047 times. `sequential_branches_join_with_branch_ensuring.md`
proves the same shape with one `branch ensuring` per branch, in work linear
in the number of branches.

```c filename=sequential_branches.c
int32 f(int32 x, int32 a0, int32 b0, int32 a1, int32 b1, int32 a2, int32 b2, int32 a3, int32 b3, int32 a4, int32 b4, int32 a5, int32 b5, int32 a6, int32 b6, int32 a7, int32 b7, int32 a8, int32 b8, int32 a9, int32 b9, int32 a10, int32 b10) {
    if (a0 >= b0) { x = x + 1; }
    if (a1 >= b1) { x = x + 1; }
    if (a2 >= b2) { x = x + 1; }
    if (a3 >= b3) { x = x + 1; }
    if (a4 >= b4) { x = x + 1; }
    if (a5 >= b5) { x = x + 1; }
    if (a6 >= b6) { x = x + 1; }
    if (a7 >= b7) { x = x + 1; }
    if (a8 >= b8) { x = x + 1; }
    if (a9 >= b9) { x = x + 1; }
    if (a10 >= b10) { x = x + 1; }
    return x;
}
```

```click
verifying "sequential_branches.c";

int32 f(int32 x, int32 a0, int32 b0, int32 a1, int32 b1, int32 a2, int32 b2, int32 a3, int32 b3, int32 a4, int32 b4, int32 a5, int32 b5, int32 a6, int32 b6, int32 a7, int32 b7, int32 a8, int32 b8, int32 a9, int32 b9, int32 a10, int32 b10) {
    requires x >= 0 and x < 1000;
    ensures result >= 0;
}
```

```expect
fail: the implicit tail split at more than 1024 C branches
```
