# A library field function of a constructed value is not its field unopened

`slice::len(Slice<uint8>::Slice(p, m))` lowers as the call that was written.
Proving `slice::len(Slice<uint8>::Slice(p, m)) == m` requires exposing the
definition with `unfold`.

```click
import click::rust::slice;

theorem unopened(p: uint8*, m: uint64) {
    ensures slice::len(Slice<uint8>::Slice(p, m)) == m by {
        close() using {};
    }
}
```

```expect
fail: `close() using` could not prove the current goal from only its listed premises
```
