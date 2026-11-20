# C automatic objects have source declaration references

```c filename=declarations.c
int identity(int x, int choice) {
    int y = x;
    if (choice) { int x = 7; int y = x; }
    return y;
}
```

```click
verifying "declarations.c";
int32 identity(int32 x, int32 choice) {
    ensures result == old(identity.parameter(0));
} by {
    step_until(statement(1).entry);
    have identity.local(0) == identity.statement(0).local(y) by { known(); }
    have identity.local(0) == identity.parameter(0) by { known(); }
    if identity.parameter(1) != 0 {
        step_until(function.exit);
        known();
    } else {
        step_until(function.exit);
        known();
    }
}
```

```expect
pass
```
