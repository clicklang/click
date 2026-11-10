# A quantified fact over a function's result matches a renamed binder

A universal's binder is fresh each time the universal is lowered, so a stated
`forall` meets the same `forall` owed elsewhere only up to that renaming. The
renaming reaches a binder among the arguments of a function whose result is
a slice or a pointer, such as the chunk a library iterator yields at an
index. Each quantified invariant below is closed at loop entry by the
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
import click::rust::chunks_exact;
verifying "walk.c";

unsigned long walk(unsigned char *p, unsigned long n) {
    ensures result == n;
} by {
    step_until(loop(0));
    loop {
        decreases n - i;
        invariant i <= n;
        invariant forall (j: uint64) {
            j < n / 4u64 implies
                chunks_exact::nth(chunks_exact::chunks_exact(Slice<uint8>::Slice(p, n), 4u64), j).len() == 4u64
        };
        invariant forall (j: uint64) {
            j < n / 4u64 implies
                chunks_exact::nth(chunks_exact::chunks_exact(Slice<uint8>::Slice(p, n), 4u64), j).as_ptr()
                    == p + j * 4u64
        };
        initialize by {
            have forall (j: uint64) {
                j < n / 4u64 implies
                    chunks_exact::nth(chunks_exact::chunks_exact(Slice<uint8>::Slice(p, n), 4u64), j).len() == 4u64
            } by {
                intro();
                intro();
                apply(chunks_exact::nth_chunks_exact(Slice<uint8>::Slice(p, n), 4u64, j));
            }
            have forall (j: uint64) {
                j < n / 4u64 implies
                    chunks_exact::nth(chunks_exact::chunks_exact(Slice<uint8>::Slice(p, n), 4u64), j).as_ptr()
                        == p + j * 4u64
            } by {
                intro();
                intro();
                apply(chunks_exact::nth_chunks_exact(Slice<uint8>::Slice(p, n), 4u64, j));
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
