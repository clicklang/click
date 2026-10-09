# A loop proof certifies its contract in authority mode

The certified path belongs to the function with its loop annotations; the
entry resource transfer, checked from the same signature and contract, does
not make certification reject it.

```c filename=count_to_three.c
int32 count_to_three() {
    int32 i;
    i = 0;
    while (i < 3) {
        i = i + 1;
    }
    return i;
}
```

```click
verifying "count_to_three.c";

int32 count_to_three() {
    ensures result == 3;
} by {
    step();
    step();
    have i == 0 by {
        simp();
    }
    loop {
        decreases 3 - i;
        invariant i >= 0;
        invariant i <= 3;
    }
    step();
    simp();
}
```

```expect
pass
```
