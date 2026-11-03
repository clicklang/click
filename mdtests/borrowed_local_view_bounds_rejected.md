# a borrowed view of a caller's local must fit that local

The caller owns its declared local array. A callee's `views` requirement must
fit that ownership: a range running past the block must not be admitted through
implicit local-storage authority just because the allocation exists.

Here the callee views three elements of a two-element array, and reads the
third. The call is rejected rather than discharged by the block merely
existing.

```c filename=borrowed_local_view_bounds_rejected.c
int32 third(int32* values) {
    return values[2];
}

int32 borrowed_local_view_bounds_rejected() {
    int32 pair[2];
    int32 tail = 9;
    pair[0] = 1;
    pair[1] = 2;
    return third(pair) * 0 + tail;
}
```

```click
verifying "borrowed_local_view_bounds_rejected.c";

int32 third(int32* values) {
    views values[0..3];
    ensures result == values[2];
}

int32 borrowed_local_view_bounds_rejected() {
    ensures result == 9;
}
```

```expect
fail: selected resource `views pair[0..3]`
```
