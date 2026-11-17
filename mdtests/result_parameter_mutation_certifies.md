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
    requires 0 <= program::result and program::result <= 100;
    ensures result == program::result + 1 and result == old(program::result) + 1;
}
```

```expect
pass
```
