# a have without a proof is simp

A `have` states a fact where it is written, so an omitted proof is `simp` at
that point. It does not execute C: the first `have` below is proved before
any statement runs, and the first `step()` still starts at the declaration.

```c filename=add_one.c
int add_one(int x) {
    int y = x + 1;
    return y;
}
```

```click
verifying "add_one.c";

int32 add_one(int32 x) {
    requires 0 <= x;
    requires x < 100;
    ensures result == x + 1;
} by {
    have x < 101;
    step();
    step();
    have y == x + 1;
    execute();
    simp();
}
```

```expect
pass
```
