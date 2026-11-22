# A byte-view holding supplies a read its reader has bounds for

`copy`'s contract states its effect through `destination as (uint8*)`, which
forms the byte view of the allocation (C11 6.3.2.3p7), so the bytes it
produces are held through that wider view. Reading `destination[0]` afterwards
goes through the caller's own parameter, whose bounds are opaque. The read
needs two separate things: the bytes, which the byte-view holding of the same
provenance supplies, and bounds for `destination` that contain them, which the
entry clause `owns uninitialized(destination[0..1])` established. This is the
shape of C++'s `memcpy` contract (`library/cpp/memcpy.interface.click`).
Bytes beyond that evidence stay refused even when held
(`kernel::assumptions::pointer_domains::scaling_tests::a_broader_holding_supplies_bytes_its_reader_has_coverage_for`).

```c filename=copy.c
void* copy(void* destination, const void* source, unsigned long bytes);
unsigned char probe(unsigned char* destination, const unsigned char* source) {
    copy(destination, source, 1);
    return destination[0];
}
```

```click
import click::bytes;
verifying "copy.c";
extern void* copy(void* destination, const void* source, uint64 bytes) {
    views (source as (const uint8*))[0..bytes];
    consumes uninitialized((destination as (uint8*))[0..bytes]);
    produces (destination as (uint8*))[0..bytes];
    ensures result == destination;
    ensures bytes::equal(destination as (uint8*), 0u64, old(source as (const uint8*)), 0u64, bytes);
}
uint8 probe(uint8* destination, const uint8* source) {
    owns uninitialized(destination[0..1]);
    views source[0..1];
    ensures result == old(source[0]);
} by {
    step();
    have destination[0] == old(source[0]) by {
        instantiate(forall (k: uint64) {
            true and k < 1u64 implies destination[0u64 + k] == old(source[0u64 + k])
        }, 0u64);
        solve();
    }
    step_until(function.exit);
}
```

```expect
pass
```
