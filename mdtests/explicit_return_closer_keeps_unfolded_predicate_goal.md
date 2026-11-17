# An explicit return closer keeps the unfolded predicate goal

The contract names the predicate, while the proof establishes its body.
The local unfold must refine the current claim, so its closer sees the body.

```c filename=echo.c
int32 echo(int32 x) { return x; }
```

```click
predicate same(a: int32, b: int32) { a == b }

verifying "echo.c";

int32 echo(int32 x) {
    ensures same(result, x);
} by {
    step();
    unfold(same(result, x));
    known();
}
```

```expect
pass
```
