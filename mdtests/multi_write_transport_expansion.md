# A multi-write transport expands to ordinary steps

```c filename=keep.c
void keep(unsigned char *p, unsigned char *q) { *p = 0; *p = 1; }
```

```click
verifying "keep.c";
void keep(uint8* p, uint8* q) {
    owns *p;
    views *q;
    requires separate(memory(*p), memory(*q));
} by {
    step();
    have separate(statement(0).footprint, memory(*q)) by {
        close() using { separate(memory(*p), memory(*q)); };
    }
    step();
    have separate(statement(1).footprint, memory(*q)) by {
        close() using { separate(memory(*p), memory(*q)); };
    }
    have *q == at(statement(0).entry, *q) by {
        transport(at(statement(0).entry, *q) == at(statement(0).entry, *q),
            *q == at(statement(0).entry, *q));
    }
    step();
}
```

```expect
pass
```
