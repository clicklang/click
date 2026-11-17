# Unsigned array initializers reject out of bounds

Unsigned elements retain the existing initializer and memory checks.

```c filename=array.c
unsigned int rejected(void) {
    unsigned int values[2] = { 10u, 20u };
    return values[2];
}
```

```click
verifying "array.c";
uint32 rejected() { ensures result == 0u32; }
```

```expect
fail: viewable(((byte_offset("array.c"::rejected.local(0).storage(implicit), 8)) as (uint8 *))[0..4])
```
