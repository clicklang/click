# An unsigned array index has spellable execution cases

The initialized cells are selected by unsigned 64-bit byte-offset equalities.
The implicit tail must be able to write those conditions as proof cases.

```c filename=read.c
int read(unsigned int x) {
    int values[2] = {3, 5};
    int r = 1;
    r = values[x];
    return r;
}
```

```click
verifying "read.c";
int32 read(uint32 x) {
    requires x < 2u32;
    ensures result == 3 or result == 5;
}
```

```expect
pass
```
