# composite resource folded memory fact projection

This checks that holding a folded composite resource exposes its memory facts
without unfolding the contained write permission.

```c filename=noop_flag.c
int32 noop_flag(int32* flag) {
    return 0;
}
```

```click
resource zero_flag(flag: int32*) {
    owns flag[0..1];
    fact flag[0] == 0;
}

verifying "noop_flag.c";

int32 noop_flag(int32* flag) {
    owns zero_flag(flag) by auto;

    ensures flag[0] == 0 by auto;
}
```

```expect
pass
```
