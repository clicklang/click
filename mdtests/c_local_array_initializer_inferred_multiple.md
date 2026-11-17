# Each declarator completes its own inferred bound

The C frontend completes the array type before emitting its existing local-array operations.

```c filename=array.c
unsigned long multiple(void) {
    int first[] = { 1 }, second[] = { 2, 3 };
    return sizeof(first) + sizeof(second);
}
```

```click
verifying "array.c";
uint64 multiple() { ensures result == 12u64; }
```

```expect
pass
```
