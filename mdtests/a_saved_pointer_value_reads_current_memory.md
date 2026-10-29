# A saved pointer value reads current memory

Indexing an old array reference reads old memory. Binding its pointer value
lets the proof read current memory at that saved address.

```c filename=probe.c
void clear(int32* p) { p[0] = 0; }
```

```click
verifying "probe.c";
void clear(int32* p) {
    owns p[0..1];
    requires p[0] == 1;
    ensures p[0] == 0;
} by {
    step();
    have (let saved: int32* = old(p); saved[0]) == 0;
    have old(p)[0] == 1;
}
```

```expect
pass
```
