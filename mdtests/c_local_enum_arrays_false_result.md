# Local enum arrays reject false result

The new enum-array admission preserves the existing integer-array checks.

```c filename=mode.c
enum mode { MODE_OFF, MODE_ON };
int rejected(void) {
    enum mode modes[2];
    modes[1] = MODE_ON;
    return modes[1];
}
```

```click
verifying "mode.c";
int32 rejected() { ensures result == 0; }
```

```expect
fail: unclosed goal
```
