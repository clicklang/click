# An explicit return closer keeps the unfolded predicate goal

The contract names the predicate, while the proof establishes its body.
Return-claim lowering must retain both forms after an explicit unfold.

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
    unfold(same);
    assumption();
}
```

```expect
pass
```
