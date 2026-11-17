# Unsigned switch labels must remain distinct after conversion

Both labels denote the same unsigned 32-bit value.

```c filename=duplicate.c
int duplicate(unsigned int value) {
    switch (value) {
        case -1: return 1;
        case 4294967295u: return 2;
        default: return 0;
    }
}
```

```click
verifying "duplicate.c";
int32 duplicate(uint32 value) { ensures result == 0; }
```

```expect
fail: duplicate `case` label value 4294967295
```
