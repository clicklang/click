# `execute_until` refuses a missing statement region

A statement region the function does not have is refused with what it does
have, as `at(...)` refuses it.

```c filename=execute_until_missing.c
int32 probe(int32 x) {
    int32 y = x;
    return y;
}
```

```click
verifying "execute_until_missing.c";

int32 probe(int32 x) {
    ensures result == x;
} by {
    execute_until(statement(0).region(3));
    execute();
    simp();
}
```

```expect
fail: so it has no `region(3)`
```
