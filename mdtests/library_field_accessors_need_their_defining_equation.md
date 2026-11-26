# A library field accessor needs its defining equation

Like a locally defined pure function, `slice::len` stays folded even when
its argument is a constructor. Expose the defining equation with
`unfold(slice::len(Slice<uint8>::Slice(p, n)))` before closing the proof.

```click
import click::rust::slice;

theorem a_slice_length_stays_a_call(p: uint8*, n: uint64) {
    ensures slice::len(Slice<uint8>::Slice(p, n)) == n by {
        close() using {};
    }
}
```

```expect
fail: `close() using` could not prove the current goal from only its listed premises
```
