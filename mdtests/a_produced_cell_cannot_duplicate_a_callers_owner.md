# A produced cell cannot duplicate the caller's owner

Returning an entry-owned borrow can restore its retained occurrence directly.
A new `produces` clause must still reject overlap with the caller's frame,
before a later call or function return happens to inspect that frame.

```c filename=duplicate_output.c
int duplicate_output(int *p) {
    mint(p);
    return 0;
}
```

```click
verifying "duplicate_output.c";
extern void mint(int32* p) {
    produces p[0..1];
}
int32 duplicate_output(int32* p) {
    consumes p[0..1];
    ensures result == 0;
}
```

```expect
fail: C operation: mint(p)
```
