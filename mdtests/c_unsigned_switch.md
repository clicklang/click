# Unsigned switch selectors retain their full 32-bit value

The original C example and its contract are unchanged.

```c filename=switch.c
int is_one(unsigned int value) {
    switch (value) {
        case 1u: return 1;
        default: return 0;
    }
}
```

```click
verifying "switch.c";
int32 is_one(uint32 value) {
    requires value == 1u32;
    ensures result == 1;
}
```

```expect
pass
```
