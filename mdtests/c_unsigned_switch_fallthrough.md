# Unsigned switch cases retain fallthrough and break

C source retains its ordinary integer types and switch control flow.

```c filename=switch.c
int fallthrough(unsigned int value) {
    int result = 0;
    switch (value) {
        case 0u: result += 1;
        case 1u: result += 2; break;
        default: result = 9; break;
    }
    return result;
}
```

```click
verifying "switch.c";
int32 fallthrough(uint32 value) {
    requires value == 0u32;
    ensures result == 3;
}
```

```expect
pass
```
