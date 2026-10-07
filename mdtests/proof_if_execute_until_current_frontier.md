# Execute until the current frontier inside a proof branch

Stopping at the statement already selected succeeds in both arms and records
no execution step. It must not decline the enclosing proof `if`.

```c filename=identity.c
int32 identity(int32 x) { return x; }
```

```click
verifying "identity.c";
int32 identity(int32 x) { ensures result == x; } by {
    if x == 0 {
        execute_until(statement(0));
        execute(); simp();
    } else {
        execute_until(statement(0));
        execute(); simp();
    }
}
```

```expect
pass
```
