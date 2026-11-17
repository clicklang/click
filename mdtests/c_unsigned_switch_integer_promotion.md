# A narrow unsigned switch selector promotes to int

C source retains its ordinary integer types and switch control flow.

```c filename=switch.c
int narrow_selector(unsigned short value) {
    switch (value) {
        case 65535: return 1;
        default: return 0;
    }
}
```

```click
verifying "switch.c";
int32 narrow_selector(uint16 value) {
    requires value == (65535 as uint16);
    ensures result == 1;
}
```

```expect
pass
```
