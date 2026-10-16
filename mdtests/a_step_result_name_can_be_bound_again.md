# A step result name can be bound again

A step's result is a proof binder, and the newest binding of a name wins.
Each `let { result: r } = step()` below names its own assignment's value, so
after the second step `r` is `old(x) + 2`, not `old(x) + 1`.

```c filename=step_result_rebound.c
int add_two(int x) {
    x = x + 1;
    x = x + 1;
    return x;
}
```

```click
verifying "step_result_rebound.c";

int add_two(int x) {
    requires x < 2147483646;
    ensures result == old(x) + 2;
} by {
    let { result: r } = step();
    have r == old(x) + 1 by simp();
    let { result: r } = step();
    have r == old(x) + 2 by simp();
    execute();
    simp();
}
```

```expect
pass
```
