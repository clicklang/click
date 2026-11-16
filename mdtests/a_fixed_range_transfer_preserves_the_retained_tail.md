# A fixed range transfer preserves the retained tail

A call returns an initialized byte range using its selected consumed owner.
The caller retains the adjacent bytes and returns ownership of the whole array.

```c filename=fixed_range_transfer.c
void caller(unsigned char *bytes) {
    initialize(bytes);
}
```

```click
verifying "fixed_range_transfer.c";

extern void initialize(uint8* bytes) {
    consumes uninitialized(bytes[0..4]);
    produces bytes[0..4];
}

void caller(uint8* bytes) {
    owns bytes[0..8];
} by {
    step();
    step();
}
```

```expect
pass
```
