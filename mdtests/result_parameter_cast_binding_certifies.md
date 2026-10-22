# A C parameter named `result` keeps its binding through casts

```c filename=bump.c
int32 bump(int32 result) {
    return result + 1;
}
```

```click
verifying "bump.c";

int32 bump(int32 result) {
    requires 0 <= c(result) and c(result) <= 100;
    ensures to_integer(result) == to_integer(((int32)c(result)) + 1) by auto();
    ensures to_integer(((int32)(c(result) + result))) == to_integer(c(result) + result) by auto();
}
```

```expect
pass
```
