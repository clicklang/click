# Existential call search keeps its witness local

The local declaration changes the state of the call requirement's view.
Searching for a witness in the entry fact used to assume `1 <= n` with
`n` still bound. The verifier should report the missing call prerequisite.

```c filename=entry_witness_view.c
int witness_view(int *p) {
    int local;
    return need_cells(p);
}
```

```click
verifying "entry_witness_view.c";

extern int32 need_cells(int32 *p) {
    requires exists (n: int32) {
        1 <= n and viewable(p[0..n])
    };
    ensures result == 0;
}

int32 witness_view(int32 *p) {
    requires exists (n: int32) {
        1 <= n and viewable(p[0..n])
    };
    ensures result == 0;
}
```

```expect
fail: `step()` requires an explicit prerequisite proof (precondition clause 1 of `need_cells`)
```
