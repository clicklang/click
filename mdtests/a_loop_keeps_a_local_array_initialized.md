# a loop keeps a local array initialized

A loop body that writes memory forgets the cached values of an automatic
array, which the body may overwrite through `a[i]`. It used to forget that
the array was written at all, so reading `a[1]` after the loop was refused as
a read of uninitialized storage. The body can only initialize more, so the
loop havoc keeps the forgotten elements' bytes in the memory's
initialization record, and the read is an initialized element of unknown
value. `mdtests/a_loop_does_not_initialize_an_element_it_never_writes.md` is
the negative next door.

```c filename=a_loop_keeps_a_local_array_initialized.c
int32 after_loop() {
    int32 a[2];
    int32 i;
    a[0] = 5;
    a[1] = 5;
    i = 0;
    while (i < 2) {
        a[i] = 7;
        i = i + 1;
    }
    return a[1];
}
```

```click
verifying "a_loop_keeps_a_local_array_initialized.c";

int32 after_loop() {
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
