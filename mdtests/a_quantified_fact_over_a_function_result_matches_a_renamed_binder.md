# A quantified fact over a function's result matches a renamed binder

A universal's binder is fresh each time the universal is lowered, so a stated
`forall` meets the same `forall` owed elsewhere only up to that renaming. The
renaming reaches a binder among the arguments of a function whose result is
a slice or a pointer, such as the slice `slice::from_raw_parts` builds
from a pointer the binder offsets. Each quantified invariant below is closed at loop entry by the
`have` its `initialize` script states.

```c filename=walk.c
unsigned long walk(unsigned char *p, unsigned long n) {
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

unsigned long walk(unsigned char *p, unsigned long n) {
    ensures result == n;
} by {
    step_until(loop(0).entry);
    loop {
        decreases n - i;
        invariant i <= n;
        invariant forall (j: uint64) {
            j < n implies
                slice::from_raw_parts(p + j, 4u64).as_ptr() == p + j
        };
        initialize by {
            have forall (j: uint64) {
                j < n implies
                    slice::from_raw_parts(p + j, 4u64).as_ptr() == p + j
            } by {
                intro();
                intro();
                close();
            }
            close();
        }
    }
    step_until(function.exit);
    close();
}
```

```expect
pass
```
