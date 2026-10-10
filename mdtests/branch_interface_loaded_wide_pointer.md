# A branch interface keeps the element type of a loaded local pointer

The 64-bit word remains unchanged while the two arms update a separate cell.
The interface must read the word through the local `unsigned long *` with its
declared width. Previously each arm proved the fact, but the checked join
lowered that local dereference as `int32` and rejected the interface.

```c filename=probe.c
struct Holder { int32 *p; unsigned long *q; };
void put(struct Holder *h, int32 x, unsigned long stamp) {
    int32 *p = h->p;
    unsigned long *q = h->q;
    *q = (unsigned long)p + stamp;
    if (x <= 0) { *p = 0; } else { *p = 1; }
}
```

```click
verifying "probe.c";
void put(struct Holder* h, int32 x, uint64 stamp) {
    owns h->p;
    owns *h->p;
    owns h->q;
    owns *h->q;
    ensures 1 == 1;
} by {
    step(); step(); step(); step(); step();
    have *q == address(p) + stamp;
    branch ensuring { fact *q == address(p) + stamp; } then {
        step(); have *q == address(p) + stamp by { simp(); }
    } else {
        step(); have *q == address(p) + stamp by { simp(); }
    }
    execute(); simp();
}
```

```expect
pass
```
