# Statement regions reach a loop body

`loop(i).statement(j)` is the `j`th statement of loop `i`'s body. The loop is
also the statement it is as written, here `statement(2)`, so
`statement(2).statement(0)` names the same point.

```c filename=statement_paths_loop.c
int32 walk(int32 n) {
    int32 i;
    i = 0;
    while (i < n) {
        i = i + 1;
    }
    return i;
}
```

```click
verifying "statement_paths_loop.c";

int32 walk(int32 n) {
    requires 0 <= n;
    ensures result == n;
} by {
    step();
    step();
    loop {
        decreases n - i;
        invariant 0 <= i and i <= n;
        initialize by { simp(); }
        preserve by {
            step();
            have i == at(loop(0).statement(0).entry, i) + 1 by simp();
            have i == at(statement(2).statement(0).entry, i) + 1 by simp();
            have at(loop(0).statement(0).entry, i) < n by simp();
            close_invariants();
        }
    }
}
```

```expect
pass
```
