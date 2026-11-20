# A typed local read keeps its write across a disjoint store

Click can name the read of an address-backed local at its write and read
the same version after a write to a different local.

```c filename=local_reads.c
int32 read(int32 value) {
    int32 slot = 0;
    int32 other = 0;
    int32* p = &slot;
    int32* q = &other;
    *p = value;
    *q = 1;
    return slot;
}
```

```click
verifying "local_reads.c";

int32 read(int32 value) {
    ensures result == value;
} by {
    step_until(statement(5).entry);
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
