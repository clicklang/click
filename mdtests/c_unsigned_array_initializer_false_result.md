# Unsigned array initializers reject false result

Unsigned elements retain the existing initializer and memory checks.

```c filename=array.c
unsigned int rejected(void) {
    unsigned int values[2] = { 10u };
    return values[1];
}
```

```click
verifying "array.c";
uint32 rejected() { ensures result == 1u32; }
```

```expect
fail: unclosed goal
```
