# A break leaves through the body proof

A constant true guard makes the false-guard exit unreachable. The
`otherwise` proof consequently has no path on which to run.

```c filename=always_break.c
void always_break(int n) {
    while (1)
        break;
}
```

```click
verifying "always_break.c";

void always_break(int32 n) {
    ensures true;
} by {
    loop {
        decreases 0;
        otherwise {
            have n == 0 by close();
        }
    }
}
```

```expect
pass
```
