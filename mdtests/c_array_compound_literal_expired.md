# Reject a use of an array compound literal after its enclosing block ends

```c filename=example.c
int answer(void) {
    int *values;
    {
        values = (int[]){10, 20, 30};
    }
    return values[1];
}
```

```click
verifying "example.c";
int32 answer() { ensures result == 20; }
```

```expect
fail: invalid memory access
```
