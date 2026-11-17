# A library field accessor needs its defining equation

Like a locally defined pure function, `slice::len` stays folded even when
its argument is a constructor. `normalize` alone does not unfold the call;
write `unfold(slice::len(Slice<uint8>::Slice(p, n)))` first.

```click
import click::rust::slice;

theorem a_slice_length_stays_a_call(p: uint8*, n: uint64) {
    ensures slice::len(Slice<uint8>::Slice(p, n)) == n by {
        normalize();
    }
}
```

```expect
fail: `normalize` goal did not normalize to true
```
