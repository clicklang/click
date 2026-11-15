# Observation uses a local pointer's element width

A local pointer does not appear in the function's parameter type table.
Selecting its held range must retain its element type instead of defaulting
to four-byte elements.

```c filename=observe-locals.c
void bytes(uint8* p) { uint8* q = p; }
void wide(uint64* p) { uint64* q = p; }
```
```click
verifying "observe-locals.c";
void bytes(uint8* p) { owns p[0..2]; } by {
    step(); step();
    have viewable(q[0..2]) by { observe(q[0..2]); }
}
void wide(uint64* p) { owns p[0..2]; } by {
    step(); step();
    have viewable(q[0..2]) by { observe(q[0..2]); }
}
```
```expect
pass
```
