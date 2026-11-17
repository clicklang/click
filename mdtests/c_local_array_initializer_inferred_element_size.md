# The element type is known while the array bound is incomplete

The C frontend completes the array type before emitting its existing local-array operations.

```c filename=array.c
int element_size(void) {
    int values[] = { sizeof(values[0]), 20 };
    return values[0];
}
```

```click
verifying "array.c";
int32 element_size() { ensures result == 4; }
```

```expect
pass
```
