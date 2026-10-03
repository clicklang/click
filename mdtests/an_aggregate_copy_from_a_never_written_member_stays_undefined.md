# an aggregate copy from a never-written member stays undefined

The negative next door to
`mdtests/an_aggregate_copy_carries_a_forgotten_initialized_field.md`. The
loop forgets the cached value of `source.tag` and the initialization record
keeps its bytes, so the copy may carry `tag`. Nothing ever wrote
`source.payload`, though, and the record holds none of its bytes: copying it
is still a read of uninitialized storage, as it is without the loop
(`mdtests/aggregate_copy_uninitialized_source_rejected.md`).

```c filename=an_aggregate_copy_from_a_never_written_member_stays_undefined.c
union payload {
    int32 number;
    int32* pointer;
};

struct packet {
    int32 tag;
    union payload payload;
};

int32 copy_after_loop() {
    struct packet source;
    struct packet destination;
    int32 i;
    source.tag = 5;
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
verifying "an_aggregate_copy_from_a_never_written_member_stays_undefined.c";

int32 copy_after_loop() {
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
fail: read of uninitialized storage
```
