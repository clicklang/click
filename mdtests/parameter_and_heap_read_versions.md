# Parameter and heap read versions

A fixed displacement from the same parameter leaves its other word intact.
A separate allocation carries its own read versions through writes and reads.

```c filename=indexed_reads.c
int32 parameter(int32 *p) {
    p[0] = 7;
    p[1] = 9;
    return p[0];
}

int32 relative(int32 *p, int32 i) {
    int32 *cursor = p + i;
    cursor[0] = 7;
    cursor[1] = 9;
    return cursor[0];
}

int32 heap(void) {
    int32 *p = malloc(8);
    if (p == 0) {
        return 0;
    }
    p[0] = 7;
    p[1] = 9;
    int32 value = p[0];
    free(p);
    return value;
}
```

```click
verifying "indexed_reads.c";

int32 parameter(int32 *p) {
    owns p[0..2];
    ensures result == 7;
} by {
    step();
    mark stored;
    step();
    have p[0] == at(stored, p[0]) by close();
    step();
    close();
}

int32 relative(int32 *p, int32 i) {
    owns p[0..4];
    requires 0 <= i;
    requires i < 3;
    ensures result == 7;
} by {
    step(); step(); step();
    mark stored;
    step();
    have cursor[0] == at(stored, cursor[0]) by close();
    step();
    close();
}

int32 heap() {
    ensures result == 0 or result == 7;
}
```

```expect
pass
```
