# Unsigned switch dispatch rejects a false high-bit result

```c filename=bad.c
int bad(unsigned int value) {
    switch (value) {
        case 4294967295u: return 7;
        default: return 0;
    }
}
```

```click
verifying "bad.c";
int32 bad(uint32 value) {
    requires value == 4294967295u32;
    ensures result == 0;
}
```

```expect
fail: unclosed goal
```
