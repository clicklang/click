# Select a named local store

`assignment(x, N)` selects the zero-based static occurrence of a local store
in executable preorder. Declarations and stores to other locals do not count.
The proof pauses before the selected store; `step()` checks the store itself.

```c filename=assignment.c
int32 stored() {
    int32 x;
    int32 other;
    other = 9;
    x = 3;
    other = 8;
    x = 4;
    return x;
}
```

```click
verifying "assignment.c";
int32 stored() {
    ensures result == 4;
} by {
    execute_until(assignment(x, 0));
    step();
    have x == 3 by { simp(); }
    execute_until(assignment(x, 1));
    have x == 3 by { simp(); }
    step();
    have x == 4 by { simp(); }
    execute(); simp();
}
```

```expect
pass
```
