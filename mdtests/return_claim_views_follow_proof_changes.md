# Return views preserve old loads across predicate and fact changes

A memory postcondition uses the entry snapshot, while the later predicate
claim needs its explicitly unfolded body. Exact closers share prepared views;
an intervening unfold or new fact starts a fresh preparation scope.

```c filename=echo.c
int32 echo(int32 x, int32* p) { return x; }
```

```click
resource cell(p: int32*) { owns p[0..1]; }
predicate same(a: int32, b: int32) { a == b }
verifying "echo.c";
int32 echo(int32 x, int32* p) {
    owns cell(p);
    ensures result == x;
    ensures same(result, x);
    ensures p[0] == old(p[0]);
} by {
    step();
    assumption();
    have x == x by normalize();
    unfold(same);
    assumption();
    normalize();
}
```

```expect
pass
```
