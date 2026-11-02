# A loop's back edge closes its invariant bundle

The `preserve` script ends after its last `step()`, and the back edge owes the
exact bundle: each invariant and, for `decreases 3 - i`, its ranking members.
Each member is closed by `solve()`, as a function's exit closes each
`ensures`. Read-safety obligations are part of the bundle, not assumptions
supplied to it.

```c filename=count.c
int32 count() {
    int32 i;
    i = 0;
    while (i < 3) {
        i = i + 1;
    }
    return i;
}
```

```click
verifying "count.c";

int32 count() { ensures result == 3; } by {
    step();
    step();
    loop {
        decreases 3 - i;
        invariant i >= 0;
        invariant i <= 3;
        initialize by solve();
        preserve by {
            mark iteration;
            step();
        }
    }
    step();
    solve();
}
```

```expect
pass
```
