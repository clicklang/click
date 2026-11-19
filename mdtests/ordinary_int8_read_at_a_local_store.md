# A signed byte read keeps its write across a disjoint store

Click can name the read of an address-backed local at its write and read
the same version after a write to a different local.

```c filename=local_reads.c
int8 read(int8 value) {
    int8 slot = 0;
    int32 other = 0;
    int8* p = &slot;
    int32* q = &other;
    *p = value;
    *q = 1;
    return slot;
}
```

```click
verifying "local_reads.c";

int8 read(int8 value) {
    ensures result == value;
} by {
    step_until(statement(5));
    mark written;
    step();
    have *p == value by solve();
    have separate(memory(*q), memory(*p)) by normalize();
    have separate(statement(5).footprint, memory(*p)) by {
        normalize() using { separate(memory(*q), memory(*p)); };
    }
    have *p == at(written, *p) by {
        preserve(memory(*p), statement(5));
    }
    step_until(function.exit);
    solve();
}
```

```expect
pass
```
