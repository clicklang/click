# An inferred array compound literal decays to a pointer

```c filename=example.c
int middle(void) {
    const int *values = (int[]){10, 20, 30};
    return values[1];
}
```

```click
verifying "example.c";
int32 middle() { ensures result == 20; }
```

```expect
pass
```
