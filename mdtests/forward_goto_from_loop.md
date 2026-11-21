# A forward goto leaves the loop before its test becomes false

```c filename=outward.c
int32 scan(void) {
    int32 state = 0;
    while (state < 3) {
        state = 2;
        goto done;
    }
    {
        int32 skipped = 99;
        state = skipped;
    }
done:
    return state;
}

int32 scan_switch(void) {
    int32 state = 0;
    while (state < 3) {
        switch (state) {
        case 0:
            state = 2;
            goto done;
        default:
            state = 77;
        }
        state = 88;
    }
    state = 99;
done:
    return state;
}

int32 cleanup(void) {
    int32 *p;
    int32 value;
    while (1) {
        p = malloc(sizeof(int32));
        if (p == 0) return -1;
        *p = 7;
        goto done;
    }
done:
    value = *p;
    free(p);
    return value;
}
```

```click
verifying "outward.c";

int32 scan() {
    ensures result == 2;
}

int32 scan_switch() {
    ensures result == 2;
}

int32 cleanup() {
    ensures result == -1 or result == 7;
}
```

```expect
pass
```
