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
    ensures result == ((int32)c(result)) + 1 by auto;
    ensures ((int32)(c(result) + result)) == c(result) + result by auto;
}
```

```expect
pass
```
