# An inferred array retains its pointer element type

The C frontend completes the array type before emitting its existing local-array operations.

```c filename=array.c
int pointers(void) {
    int number = 7;
    int *values[] = { &number };
    return *values[0];
}
```

```click
verifying "array.c";
int32 pointers() { ensures result == 7; }
```

```expect
pass
```
