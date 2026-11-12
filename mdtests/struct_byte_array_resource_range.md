# Struct byte-array ranges retain their physical element width

The view and ownership cover adjacent bytes, not adjacent four-byte cells.
The same source spelling works for a global object and a pointer parameter.

```c filename=bytes.c
struct bytes { int32 tag; uint8 data[4]; };
struct bytes global;
uint8 set_global(uint8 value) {
    global.data[2] = value;
    return global.data[1];
}
uint8 set_pointer(struct bytes* p, uint8 value) {
    p->data[2] = value;
    return p->data[1];
}
```

```click
verifying "bytes.c";
uint8 set_global(uint8 value) {
    views global.data[1..2];
    owns global.data[2..3];
    ensures global.data[2] == value;
    ensures result == old(global.data[1]);
}
uint8 set_pointer(struct bytes* p, uint8 value) {
    views p->data[1..2];
    owns p->data[2..3];
    ensures p->data[2] == value;
    ensures result == old(p->data[1]);
} by {
    have contains(memory(p->data[2..3]), memory(p->data[2])) by { normalize(); }
    have contains(memory(p->data[1..2]), memory(p->data[1..2])) by {
        apply(click::separation::contains_refl(memory(p->data[1..2])));
    }
    have separate(memory(p->data[2]), memory(p->data[1..2])) by {
        apply(click::separation::restrict(memory(p->data[2..3]), memory(p->data[1..2]), memory(p->data[2]), memory(p->data[1..2]))) using {
            separate(memory(p->data[2..3]), memory(p->data[1..2]));
            contains(memory(p->data[2..3]), memory(p->data[2]));
            contains(memory(p->data[1..2]), memory(p->data[1..2]));
        };
    }
    step() by { assumption(); }
    step_until(function.exit);
}
```

```expect
pass
```
