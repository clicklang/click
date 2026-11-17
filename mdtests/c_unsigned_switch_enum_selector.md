# An enum with unsigned compatible type is an unsigned switch selector

C source retains its ordinary integer types and switch control flow.

```c filename=switch.c
enum mode { MODE_OFF, MODE_ON };
int enum_selector(enum mode value) {
    switch (value) {
        case MODE_ON: return 1;
        default: return 0;
    }
}
```

```click
verifying "switch.c";
int32 enum_selector(uint32 value) {
    requires value == 1u32;
    ensures result == 1;
}
```

```expect
pass
```
