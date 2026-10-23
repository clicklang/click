# `execute_until` does not take a statement region yet

A statement region names points for `at(...)`. `execute_until` still takes
its targets as `region(N)`, `loop(N)`, `assignment(local, N)`, `read(N)` and
`back_edge()`, and refuses a `statement(i)` region by saying so.

```c filename=execute_until_statement.c
int32 probe(int32 x) {
    int32 y = x;
    return y;
}
```

```click
verifying "execute_until_statement.c";

int32 probe(int32 x) {
    ensures result == x;
} by {
    execute_until(statement(1));
    execute();
    simp();
}
```

```expect
fail: `execute_until` does not take a `statement(i)` region yet
```
