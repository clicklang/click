# An omitted proof runs the implicit tail

This checks an omitted proof, whose implicit tail executes from function entry
to function exit and then closes every open goal.

```c filename=increment.c
int32 increment(int32 x) {
    return x + 1;
}
```

```click
verifying "increment.c";

int32 increment(int32 x) {
    requires x < 2147483647;

    ensures to_integer(result) == to_integer(x + 1);
}
```

```expect
pass
```
