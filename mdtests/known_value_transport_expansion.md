# Known-value transport expands to ordinary steps

```c filename=keep.c
void keep(int *p, int *q) { *p = 0; }
```

```click
verifying "keep.c";
void keep(int32* p, int32* q) {
    owns *p;
    views *q;
    requires separate(memory(*p), memory(*q));
    requires *q == 7;
    ensures *q == 7;
} by {
    step();
    have separate(statement(0).footprint, memory(*q)) by {
        close() using { separate(memory(*p), memory(*q)); };
    }
    have *q == 7 by {
        close();
    }
    step();
    close();
}
```

```expect
pass
```
