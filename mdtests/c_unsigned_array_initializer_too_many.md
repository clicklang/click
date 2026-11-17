# Unsigned array initializers reject too many

Unsigned elements retain the existing initializer and memory checks.

```c filename=array.c
unsigned int rejected(void) {
    unsigned int values[2] = { 1u, 2u, 3u };
    return values[0];
}
```

```click
verifying "array.c";
uint32 rejected() { ensures result == 1u32; }
```

```expect
fail: too many initializers for `values[2]`
```
