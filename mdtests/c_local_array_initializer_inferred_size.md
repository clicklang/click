# The inferred length determines sizeof

The C frontend completes the array type before emitting its existing local-array operations.

```c filename=array.c
unsigned long inferred_size(void) {
    int values[] = { 10, 20, 30, };
    return sizeof(values);
}
```

```click
verifying "array.c";
uint64 inferred_size() { ensures result == 12u64; }
```

```expect
pass
```
