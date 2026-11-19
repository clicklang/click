# An unsigned byte read keeps its write across a disjoint store

Click can name the read of an address-backed local at its write and read
the same version after a write to a different local.

```c filename=local_reads.c
uint8 read(uint8 value) {
    uint8 slot = 0;
    int32 other = 0;
    uint8* p = &slot;
    int32* q = &other;
    *p = value;
    *q = 1;
    return slot;
}
```

```click
verifying "local_reads.c";

uint8 read(uint8 value) {
    ensures result == value;
} by {
    step_until(statement(5));
    mark written;
    step();
    have *p == value by solve();
    have *p == at(written, *p) by known();
    step_until(function.exit);
    solve();
}
```

```expect
pass
```
