# A `have` refuses a possibly overwritten read

The write `p[i] = 7` may store to `p[1]`. The nested proof still has the
execution frontier and refuses to conclude that the entry value survived.

```c filename=w.c
int32 put(int32 p[3], int32 i) {
    p[i] = 7;
    return 0;
}
```

```click
verifying "w.c";
int32 put(int32 p[3], int32 i) {
    owns p[0..3];
    requires 1 <= i and i < 3;
    requires p[1] == 6;
    ensures true;
} by {
    step();
    have p[1] == 6 by {
        close();
    }
}
```

```expect
fail: the store to `p[i]` may have written it
```
