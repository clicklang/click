# Ordinary 64-bit reads name the writes to their own objects

A disjoint store preserves a typed 64-bit read of an address-backed local.
The same rule applies whether the local is signed or unsigned.

```c filename=wide_reads.c
int64 read_signed(int64 value) {
    int64 slot = 0;
    int32 other = 0;
    int64* p = &slot;
    int32* q = &other;
    *p = value;
    *q = 1;
    return slot;
}

uint64 read_unsigned(uint64 value) {
    uint64 slot = 0;
    int32 other = 0;
    uint64* p = &slot;
    int32* q = &other;
    *p = value;
    *q = 1;
    return slot;
}
```

```click
verifying "wide_reads.c";

int64 read_signed(int64 value) {
    ensures result == value;
} by {
    step_until(statement(5).entry);
    mark written;
    step();
    have *p == value by close();
    have separate(memory(*q), memory(*p)) by close();
    have separate(statement(5).footprint, memory(*p)) by {
        close() using { separate(memory(*q), memory(*p)); };
    }
    have *p == at(written, *p) by {
        preserve(memory(*p), statement(5));
    }
    step_until(function.exit);
    close();
}

uint64 read_unsigned(uint64 value) {
    ensures result == value;
} by {
    step_until(statement(5).entry);
    mark written;
    step();
    have *p == value by close();
    have separate(memory(*q), memory(*p)) by close();
    have separate(statement(5).footprint, memory(*p)) by {
        close() using { separate(memory(*q), memory(*p)); };
    }
    have *p == at(written, *p) by {
        preserve(memory(*p), statement(5));
    }
    step_until(function.exit);
    close();
}
```

```expect
pass
```
