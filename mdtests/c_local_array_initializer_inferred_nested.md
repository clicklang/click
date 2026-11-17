# Only the outer array bound is inferred

The C frontend completes the array type before emitting its existing local-array operations.

```c filename=array.c
int nested(void) {
    int values[][3] = { { 1 }, { 2, 3 } };
    return values[1][1] + values[0][2];
}
```

```click
verifying "array.c";
int32 nested() { ensures result == 3; }
```

```expect
pass
```
