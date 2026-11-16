# A library field function of a constructed value is not its field unopened

`slice::len(Slice<uint8>::Slice(p, m))` lowers as the call that was written.
`normalize` alone does not open a call, so without an `unfold` the goal
`slice::len(Slice<uint8>::Slice(p, m)) == m` stays open.

```click
import click::rust::slice;

theorem unopened(p: uint8*, m: uint64) {
    ensures slice::len(Slice<uint8>::Slice(p, m)) == m by {
        normalize();
    }
}
```

```expect
fail: `normalize` goal did not normalize to true
```
