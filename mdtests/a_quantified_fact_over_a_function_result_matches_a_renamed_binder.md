# A quantified fact over a function's result matches a renamed binder

A universal's binder is fresh each time the universal is lowered, so a stated
`forall` meets the same `forall` owed elsewhere only up to that renaming. The
renaming reaches a binder among the arguments of a function whose result is
a slice or a pointer, such as the slice a library iterator over a slice
built from the binder holds. Each quantified invariant below is closed at loop entry by the
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
import click::rust::slice_iter;
verifying "walk.c";

unsigned long walk(unsigned char *p, unsigned long n) {
    ensures result == n;
} by {
    step_until(loop(0));
    loop {
        decreases n - i;
        invariant i <= n;
        invariant forall (j: uint64) {
            j < n implies
                slice_iter::as_slice(slice_iter::iter(Slice<uint8>::Slice(p + j, 4u64)))
                    == Slice<uint8>::Slice(p + j, 4u64)
        };
        initialize by {
            have forall (j: uint64) {
                j < n implies
                    slice_iter::as_slice(slice_iter::iter(Slice<uint8>::Slice(p + j, 4u64)))
                        == Slice<uint8>::Slice(p + j, 4u64)
            } by {
                intro();
                intro();
                apply(slice_iter::as_slice_iter(Slice<uint8>::Slice(p + j, 4u64)));
            }
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
