# an aggregate copy carries a forgotten initialized field

Whole-struct assignment copies every member (C11 6.5.16.1p2), and a
union-containing layout routes it through the kernel's aggregate copy. The
copy used to ask each source field for its cached value and, finding none in
automatic storage, report a read of uninitialized storage. A loop that may
write `source.tag` forgets that cached value, but not that `source.tag` was
written: its bytes stay in the memory's initialization record. The copy now
consults the record and carries the field's unknown value as a typed load of
the source, and the destination is initialized in turn, so the read below
is an initialized value the loop leaves open.
`mdtests/an_aggregate_copy_from_a_never_written_member_stays_undefined.md` is
the negative next door.

```c filename=an_aggregate_copy_carries_a_forgotten_initialized_field.c
union payload {
    int32 number;
    int32* pointer;
};

struct packet {
    int32 tag;
    union payload payload;
};

struct packet g;

int32 copy_after_loop() {
    struct packet source;
    struct packet destination;
    int32 i;
    source = g;
    i = 0;
    while (i < 2) {
        source.tag = 7;
        i = i + 1;
    }
    destination = source;
    return destination.tag;
}
```

```click
verifying "an_aggregate_copy_carries_a_forgotten_initialized_field.c";

int32 copy_after_loop() {
    owns g.tag;
    owns g.payload.number;
    requires g.tag == 1;
    requires g.payload.number == 2;
    ensures result == result;
} by {
    step();
    step();
    step();
    step();
    step();
    loop {
        decreases 2 - i;
        invariant i >= 0;
        invariant i <= 2;
    }
    execute();
    simp();
}
```

```expect
pass
```
