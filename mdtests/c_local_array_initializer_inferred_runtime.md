# Runtime expressions determine values without determining the bound

The C frontend completes the array type before emitting its existing local-array operations.

```c filename=array.c
int runtime(int first, int second) {
    int values[] = { first, second };
    return values[1];
}
```

```click
verifying "array.c";
int32 runtime(int32 first, int32 second) { ensures result == second; }
```

```expect
pass
```
