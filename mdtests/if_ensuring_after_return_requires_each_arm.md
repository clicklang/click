# Each live arm must prove the return join interface

The negative arm holds the opposite inequality, so it cannot supply the join fact.

```c filename=if_ensuring_after_return.c
int32 id(int32 x) { return x; }
```

```click
verifying "if_ensuring_after_return.c";

int32 id(int32 x) {
    ensures result <= 0 or result > 0;
} by {
    step_until(function.exit);
    if result <= 0 ensuring { fact result <= 0; } then {
        have result <= 0 or result > 0 by close();
    } else {
        have result <= 0 or result > 0 by close();
    }
    close();
}
```

```expect
fail: requires the current goal as an available semantic fact
```
