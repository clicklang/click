# Local enum arrays reject out of bounds

The new enum-array admission preserves the existing integer-array checks.

```c filename=mode.c
enum mode { MODE_OFF, MODE_ON };
int rejected(void) {
    enum mode modes[2];
    modes[2] = MODE_ON;
    return 0;
}
```

```click
verifying "mode.c";
int32 rejected() { ensures result == 0; }
```

```expect
fail: <modes+8 is writable (4 bytes)>
```
