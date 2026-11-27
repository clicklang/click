# A slice built from its parts reads them in place

A slice is a built-in value, one wide pointer: its data pointer and its
length (`design/rust-slice-values.md`). `slice::len` and `slice::as_ptr`
read those components in place, so the length of
`slice::from_raw_parts(p, n)` is `n` itself and its data pointer is `p`,
with no definition to unfold. A slice is the slice built from its own
components. Before, `Slice<T>` was a library enum and each was a call that
needed `unfold`.

```click
import click::rust::slice;

theorem components_of_a_construction(p: uint8*, n: uint64) {
    ensures slice::len(slice::from_raw_parts(p, n)) == n by {
        close() using {};
    }
    ensures slice::as_ptr(slice::from_raw_parts(p, n)) == p by {
        close() using {};
    }
}

theorem a_slice_from_its_components(s: Slice<uint8>) {
    ensures slice::from_raw_parts(slice::as_ptr(s), slice::len(s)) == s by {
        close() using {};
    }
}
```

```expect
pass
```
