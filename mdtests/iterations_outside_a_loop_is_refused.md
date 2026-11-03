# Iterations outside a loop is refused

`iterations` names a pass count only inside a loop's own clauses and phases.

```c filename=iter.c
int32 doubled(int32 n) {
    int32 i;
    int32 total;
    i = 0;
    total = 0;
    while (i < n) {
        total = total + 2;
        i = i + 1;
    }
    return total;
}
```

```click
verifying "iter.c";

int32 doubled(int32 n) {
    requires n >= 0 and n <= 1000;
    ensures result == 2 * n and iterations == 0;
} by {
    step();
}
```

```expect
fail: unknown name `iterations`
```
