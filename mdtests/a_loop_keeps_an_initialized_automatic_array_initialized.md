# a loop keeps an initialized automatic array initialized

`int32 a[4] = {1};` zero-fills the array as one run of cells rather than a
cell per element. A loop body that writes `a[i]` forgets the run's values,
and it used to drop the run without recording that its elements were
written, so reading `a[3]` after the loop was refused as a read of
uninitialized storage. The declaration's initializer writes every byte of
its object (C11 6.7.9p21), so the declaration now records the whole object
in the memory's initialization record, and a run a havoc drops as a whole
records its slots too. The read is an initialized element of unknown value.
The second function does the same for an array of structs, whose fields are
runs strided by the struct's size; its loop writes only `items[0].x`, but the
havoc forgets every run all the same.
`mdtests/a_loop_does_not_initialize_an_array_beside_an_initialized_one.md` is
the negative next door.

```c filename=a_loop_keeps_an_initialized_automatic_array_initialized.c
struct point {
    int32 x;
    int32 y;
};

int32 after_loop() {
    int32 a[4] = {1};
    int32 i;
    i = 0;
    while (i < 2) {
        a[i] = 7;
        i = i + 1;
    }
    return a[3];
}

int32 after_struct_loop() {
    struct point items[100000] = {{1, 2}};
    int32 i;
    i = 0;
    while (i < 2) {
        items[0].x = i;
        i = i + 1;
    }
    return items[99999].y;
}
```

```click
verifying "a_loop_keeps_an_initialized_automatic_array_initialized.c";

int32 after_loop() {
    ensures result == result;
} by {
    step();
    step();
    step();
    step();
    loop {
        decreases 2 - i;
        invariant i >= 0;
        invariant i <= 2;
    }
    step();
    simp();
}

int32 after_struct_loop() {
    ensures result == result;
} by {
    step();
    step();
    step();
    step();
    step();
    loop {
        decreases 2 - i;
        invariant i >= 0;
        invariant i <= 2;
    }
    step();
    simp();
}
```

```expect
pass
```
