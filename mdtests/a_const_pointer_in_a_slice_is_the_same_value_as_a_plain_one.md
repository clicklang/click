# A const pointer in a slice or an equality is the same value as a plain one

`const` belongs to the expression that names a pointer, not to the pointer.
A slice built from a `const unsigned char *` parameter, and an equality that
mentions one, is the same term whichever part of a proof reads it: the
function's `requires`, a `have` in a loop's `initialize` script, and the
loop's invariant below all state one fact, and each closes the next.

```c filename=walk.c
unsigned long walk(const unsigned char *p, unsigned long n) {
    unsigned long i = 0;
    while (i < n) {
        i = i + 1;
    }
    return i;
}
```

```click
import click::rust::slice;
verifying "walk.c";

unsigned long walk(const unsigned char *p, unsigned long n) {
    requires forall (j: uint64) { j < n implies slice::from_raw_parts(p + j, n).as_ptr() == p + j };
    ensures result == n;
} by {
    step_until(loop(0));
    loop {
        decreases n - i;
        invariant i <= n;
        invariant forall (j: uint64) { j < n implies slice::from_raw_parts(p + j, n).as_ptr() == p + j };
        initialize by {
            have forall (j: uint64) { j < n implies slice::from_raw_parts(p + j, n).as_ptr() == p + j };
            solve();
        }
    }
    step_until(function.exit);
    solve();
}
```

```expect
pass
```
