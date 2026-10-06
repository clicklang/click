# A reassigned C parameter keeps its logical input binding

```c filename=bump.c
int32 bump(int32 result) {
    result = result + 1;
    return result;
}
```

```click
verifying "bump.c";

int32 bump(int32 result) {
    requires 0 <= c(result) and c(result) <= 100;
    ensures result == c(result) + 1 and result == old(c(result)) + 1 by auto;
}
```

```expect
pass
```
