# Separately returned cells remain usable as one call footprint

Constructing a call's returned resources retains its declared occurrences.
The next call can borrow their combined footprint without an automatic
normalization search over pointer aliases. The caller can then return that
same footprint.

```c filename=returned_cells.c
int caller(int *p) {
    mint(p);
    use_pair(p);
    return 0;
}
```

```click
verifying "returned_cells.c";

extern void mint(int32* p) {
    consumes uninitialized(p[0..2]);
    produces p[0..1];
    produces p[1..2];
}

extern void use_pair(int32* p) {
    owns p[0..2];
}

int32 caller(int32* p) {
    consumes uninitialized(p[0..2]);
    produces p[0..2];
    ensures result == 0;
} by {
    step();
    step();
    step();
}
```

```expect
pass
```
