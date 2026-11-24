# A call result in a loop is spelled by its loop path

A call inside a loop body is named from the loop, as its stepping points are:
`loop(0).statement(0).call(next, 0)`. Its value is
`loop(0).statement(0).call(next, 0).result`, the same call as the written
`statement(2).statement(0).call(next, 0).result`.

```c filename=loop_call_result.c
int32 next(int32 i) {
    return i + 1;
}

int32 walk(int32 n) {
    int32 i;
    i = 0;
    while (i < n) {
        i = next(i);
    }
    return i;
}
```

```click
verifying "loop_call_result.c";

int32 next(int32 i) {
    requires i < 2147483647;
    ensures result == i + 1;
}

int32 walk(int32 n) {
    requires 0 <= n;
    ensures result == n;
} by {
    step();
    step();
    loop {
        decreases n - i;
        invariant 0 <= i and i <= n;
        initialize by { close(); }
        maintain by {
            step();
            have loop(0).statement(0).call(next, 0).result == at(loop(0).statement(0).entry, i) + 1 by close();
            have statement(2).statement(0).call(next, 0).result == loop(0).statement(0).call(next, 0).result by close();
        }
    }
}
```

```expect
pass
```
