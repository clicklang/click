# Jumping out of a loop ends its local object's lifetime

```c filename=goto_scope.c
int32 scan(void) {
    int32 *p;
    while (1) {
        int32 local = 7;
        p = &local;
        goto done;
    }
done:
    return *p;
}
```

```click
verifying "goto_scope.c";

int32 scan() {
    ensures result == 7;
}
```

```expect
fail: invalid memory access
```
