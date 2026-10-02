# Select a loop entry without counting prefix statements

`execute_until(loop(0))` executes the checked prefix and stops at the loop
entry. Its expansion records the same explicit steps as a statement target.

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
    requires 0 <= n;
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
