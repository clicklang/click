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
    ensures to_integer(result) == to_integer((c(result) as int32) + 1);
    ensures to_integer(((c(result) + result) as int32)) == to_integer(c(result) + result);
}
```

```expect
pass
```
