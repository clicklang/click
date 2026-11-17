# A negative case label converts to the unsigned selector type

C source retains its ordinary integer types and switch control flow.

```c filename=switch.c
int negative_label(unsigned int value) {
    switch (value) {
        case -1: return 7;
        default: return 9;
    }
}
```

```click
verifying "switch.c";
int32 negative_label(uint32 value) {
    requires value == 4294967295u32;
    ensures result == 7;
}
```

```expect
pass
```
