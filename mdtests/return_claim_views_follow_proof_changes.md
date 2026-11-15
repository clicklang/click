# Return views preserve old loads across predicate and fact changes

A memory postcondition uses the entry snapshot, while the later predicate
claim needs its explicitly unfolded body. Each predicate claim opens its own application. Other closers retain the
entry and exit views used by the memory claim.

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
    ensures same(result, x) by { step_until(function.exit); unfold(same(result, x)); normalize(); }
    ensures p[0] == old(p[0]);
} by {
    step();
    known();
    have x == x by normalize();
    known();
}
```

```expect
pass
```
