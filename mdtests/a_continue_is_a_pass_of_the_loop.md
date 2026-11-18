# A continue is a pass of the loop

A `continue` is a back edge: the pass it ends counts. The preservation proof
selects the C branch and leaves the `continue` to the automatic tail.

```c filename=cont.c
int32 evens(int32 n) {
    int32 i;
    int32 e;
    i = 0;
    e = 0;
    while (i < n) {
        i = i + 1;
        if (i % 2 == 1) {
            continue;
        }
        e = e + 1;
    }
    return e;
}
```

```click
verifying "cont.c";

int32 evens(int32 n) {
    requires n >= 0 and n <= 1000;
    ensures result <= n;
} by {
    step();
    step();
    step();
    step();
    loop {
        decreases n - i;
        invariant 0 <= i and i <= n;
        invariant i == iterations;
        invariant 0 <= e and e <= iterations;
        preserve by {
            step();
            if i % 2 == 1 {
                step();
            } else {
                step();
                step();
            }
        }
    }
}
```

```expect
pass
```
