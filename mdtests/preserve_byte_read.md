# Preservation of a separated byte read

```c filename=keep.c
void keep(unsigned char *p, unsigned char *q) { *p = 0; }
```

```click
verifying "keep.c";
void keep(uint8* p, uint8* q) {
    owns *p;
    views *q;
    requires separate(memory(*p), memory(*q));
} by {
    step() by { known(); }
    have separate(statement(0).footprint, memory(*q)) by {
        normalize() using { separate(memory(*p), memory(*q)); };
    }
    have *q == at(statement(0).entry, *q) by {
        preserve(separate(statement(0).footprint, memory(*q)));
    }
    step_until(function.exit);
    known();
    known(); known(); known();
}
```

```expect
pass
```
