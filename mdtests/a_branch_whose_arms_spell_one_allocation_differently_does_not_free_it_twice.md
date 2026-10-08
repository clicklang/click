# A branch whose arms spell one allocation differently does not free it twice

One arm passes the allocation through `same`, whose result is a new spelling
of `p`; the other keeps `p`. The two `free` calls after the `if` then release
one allocation twice, so the function must not verify.

The kernel's memory join keys live allocations by pointer spelling, and could
hold this allocation live under both spellings. The proof never gets that far.
A `branch` requires both arms to abstract to the same successor state, and
arms that hold the allocation under different spellings do not. Past the join,
`free` also consumes the `allocation` resource, of which there is only one.

```c filename=spelled_twice.c
int32* same(int32* p) {
    return p;
}

int32 twice(int32* p, int32 flag) {
    int32* s;
    if (flag != 0) {
        s = same(p);
    } else {
        s = p;
    }
    free(s);
    free(p);
    return 0;
}
```

```click
resource allocated(p: int32*) {
    owns allocation(p, 4);
    owns p[0..1];
}

verifying "spelled_twice.c";

int32* same(int32* p) {
    consumes allocated(p);
    produces allocated(result);
    ensures result == p;
} by {
    unfold(allocated(p));
    execute();
    fold(allocated(result));
    simp();
}

int32 twice(int32* p, int32 flag) {
    consumes allocated(p);
    ensures result == 0;
} by {
    step();
    branch ensuring {
        owns allocated(s);
    } then {
        step();
    } else {
        step();
        unfold(allocated(p));
        fold(allocated(s));
    }
    unfold(allocated(s));
    step();
    step();
    step();
    simp();
}
```

```expect
fail: `branch ensuring` arms produced different abstract successor states
```
