# A shadowing inferred array uses its own completed bound

The C frontend completes the array type before emitting its existing local-array operations.

```c filename=array.c
unsigned long shadow(void) {
    int values[9];
    unsigned long outer_size = sizeof(values);
    {
        int values[] = { 10, 20 };
        return outer_size + sizeof(values);
    }
}
```

```click
verifying "array.c";
uint64 shadow() { ensures result == 44u64; }
```

```expect
pass
```
