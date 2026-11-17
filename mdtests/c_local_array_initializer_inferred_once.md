# A runtime initializer executes once

The C frontend completes the array type before emitting its existing local-array operations.

```c filename=array.c
int bump(int *count) {
    *count = *count + 1;
    return *count;
}
int once(void) {
    int count = 0;
    int values[] = { bump(&count) };
    return count + values[0];
}
```

```click
verifying "array.c";
int32 bump(int32 *count) {
    owns *count;
    requires *count < 2147483647;
    ensures *count == old(*count) + 1;
    ensures result == *count;
}
int32 once() { ensures result == 2; }
```

```expect
pass
```
