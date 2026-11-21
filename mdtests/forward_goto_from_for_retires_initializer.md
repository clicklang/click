# Jumping out of a for loop ends the initializer object's lifetime

```c filename=for_scope.c
int32 scan(void) {
    int32 *p;
    for (int32 local = 7; ; ) {
        p = &local;
        goto done;
    }
done:
    return *p;
}
```

```click
verifying "for_scope.c";

int32 scan() {
    ensures result == 7;
}
```

```expect
fail: invalid memory access
```
