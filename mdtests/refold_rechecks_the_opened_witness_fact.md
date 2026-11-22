# Refolding checks the body even when the opening supplied its witness

The block writes a value that violates the body fact. The old value of the
cell cannot justify the closing fold.

```c filename=refold_witness_rechecks.c
void bad_write(int32 *p) { *p = 8; }
```

```click
verifying "refold_witness_rechecks.c";

resource tagged(p: int32*) {
    field tag: int32;
    owns *p;
    let base: int32* where base == p and *p == 7;
}

void bad_write(int32* p) {
    owns r: tagged(p);
} by {
    with(r) { step(); }
}
```

```expect
fail: body is not established
```
