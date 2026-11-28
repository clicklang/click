# A proof if can establish a fact interface after return

The two proof arms establish the same interface and the continuation runs
once on the original return outcome.

```c filename=if_ensuring_after_return.c
int32 id(int32 x) { return x; }
```

```click
verifying "if_ensuring_after_return.c";

int32 id(int32 x) {
    ensures result <= 0 or result > 0;
} by {
    step_until(function.exit);
    if result <= 0 ensuring { fact result <= 0 or result > 0; } then {
        close();
    } else {
        close();
    }
    close();
}
```

```expect
pass
```
