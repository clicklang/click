# A loop that writes other storage keeps a calloc zero reading

The positive control for
`a_loop_that_writes_calloc_storage_forgets_its_zero_reading.md`. The loop
may write only the memory the function owns where it is entered, `other`,
and the allocation holds no cached value for the loop head to forget, so its
zero reading survives and `p[0]` reads as zero after the loop.

```c filename=a_loop_that_writes_other_storage_keeps_a_calloc_zero_reading.c
int32 other[4];

int32 f() {
    int32* p;
    int32 i;
    int32 first;
    p = calloc(2, sizeof(int32));
    if (p == 0) {
        return 0;
    }
    i = 0;
    while (i < 4) {
        other[i] = 9;
        i = i + 1;
    }
    first = p[0];
    free(p);
    return first;
}
```

```click
verifying "a_loop_that_writes_other_storage_keeps_a_calloc_zero_reading.c";

int32 f() {
    owns other[0..4];
    ensures result == 0;
} by {
    step();
    step();
    step();
    step();
    branch {
        ensuring {
            fact 1 == 1;
        }
        then {
            step();
            simp();
        }
        else {
        }
    }
    step();
    loop {
        decreases 4 - i;
        invariant i >= 0;
        invariant i <= 4;
    }
    execute();
    simp();
}
```

```expect
pass
```
