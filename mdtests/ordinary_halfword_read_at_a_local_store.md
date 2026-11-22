# Halfword reads keep their write across a disjoint store

A comparison can promote both reads to `int32` while each read retains its own type and write.

```c filename=local_reads.c
int16 read_int16(int16 value) {
    int16 slot = 0;
    int32 other = 0;
    int16* p = &slot;
    int32* q = &other;
    *p = value;
    *q = 1;
    return slot;
}

uint16 read_uint16(uint16 value) {
    uint16 slot = 0;
    int32 other = 0;
    uint16* p = &slot;
    int32* q = &other;
    *p = value;
    *q = 1;
    return slot;
}
```

```click
verifying "local_reads.c";

int16 read_int16(int16 value) {
    ensures result == value;
} by {
    step_until(statement(5).entry);
    mark written;
    step();
    have *p == value by solve();
    have separate(memory(*q), memory(*p)) by known();
    have separate(statement(5).footprint, memory(*p)) by {
        solve() using { separate(memory(*q), memory(*p)); };
    }
    have *p == at(written, *p) by {
        preserve(memory(*p), statement(5));
    }
    step_until(function.exit);
    solve();
}

uint16 read_uint16(uint16 value) {
    ensures result == value;
} by {
    step_until(statement(5).entry);
    mark written;
    step();
    have *p == value by solve();
    have separate(memory(*q), memory(*p)) by known();
    have separate(statement(5).footprint, memory(*p)) by {
        solve() using { separate(memory(*q), memory(*p)); };
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
