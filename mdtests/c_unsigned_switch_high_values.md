# Unsigned switch dispatch preserves the high bit and default case

C source retains its ordinary integer types and switch control flow.

```c filename=switch.c
int classify(unsigned int value) {
    switch (value) {
        case 0u: return 10;
        case 2147483648u: return 20;
        case 4294967295u: return 30;
        default: return 40;
    }
}
```

```click
verifying "switch.c";
int32 classify(uint32 value) {
    ensures value == 0u32 implies result == 10;
    ensures value == 2147483648u32 implies result == 20;
    ensures value == 4294967295u32 implies result == 30;
    ensures value != 0u32 and value != 2147483648u32 and value != 4294967295u32 implies result == 40;
}
```

```expect
pass
```
