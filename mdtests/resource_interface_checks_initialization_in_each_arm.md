# A resource interface checks read initialization before abstracting its arms

A logical value equation and viewability do not initialize the resource
argument. The interface must reject it in the concrete arm, before any
already-checked interface is published at the join.

```c filename=interface_initialization.c
void probe(int32 *p, int32 x) {}
```

```click
verifying "interface_initialization.c";
resource label(value: int32) {
    field unit: int32;
    fact unit == 0;
}
void probe(int32 *p, int32 x) {
    owns uninitialized(p[0..1]);
    requires p[0] == 0;
    ensures true;
} by {
    if x == 0 ensuring {
        owns t: label(p[0]);
    } then {
        let t = fold(label(0), { unit: 0 });
    } else {
        let t = fold(label(0), { unit: 0 });
    }
}
```

```expect
fail: missing pure fact: defined
```
