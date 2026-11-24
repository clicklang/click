# An unsigned local read keeps its write across a disjoint store

Click can name the read of an address-backed local at its write and read
the same version after a write to a different local.

```c filename=local_reads.c
uint32 read(uint32 value) {
    uint32 slot = 0;
    int32 other = 0;
    uint32* p = &slot;
    int32* q = &other;
    *p = value;
    *q = 1;
    return slot;
}
```

```click
verifying "local_reads.c";

uint32 read(uint32 value) {
    ensures result == value;
} by {
    step_until(statement(5).entry);
    mark written;
    step();
    have *p == value by close();
    have *p == at(written, *p) by close();
    step_until(function.exit);
    close();
}
```

```expect
pass
```
