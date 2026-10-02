# Close a singleton counter interval after a zero-iteration loop

The guard is false initially. The abstract loop proof still establishes the
counter equals the bound from its signed interval and the bound's exact value.

```c filename=loop_entry.c
int32 count(int32 n) {
    int32 i;
    i = 0;
    while (i < n) {
        i = i + 1;
    }
    return i;
}
```

```click
verifying "loop_entry.c";
int32 count(int32 n) {
    requires n == 0;
    ensures result == n;
} by {
    execute_until(loop(0));
    loop {
        decreases n - i;
        invariant 0 <= i and i <= n;
    }
    execute(); simp();
}
```

```expect
pass
```
