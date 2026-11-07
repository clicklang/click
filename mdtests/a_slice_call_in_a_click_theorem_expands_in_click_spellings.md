# A slice call in a Click theorem expands in Click spellings

A theorem written in Click syntax reads the slice library's calls as calls:
`slice::len(Slice<uint8>::Slice(p + k, n - k))`. Only a function written in
Rust syntax reads Rust's methods, such as `s.len()`, back. Before, every
proof printed slice calls in Rust spellings, so `click expand` wrote
`slice::from_raw_parts(&p[k], n - k).len()` into this theorem, and the
expansion did not verify.

```click
import click::rust::slice;

theorem slice_length_under_a_guard(p: uint8*, n: uint64) {
    requires n == 4u64;
    ensures forall (k: uint64) { k <= 4u64 implies slice::len(Slice<uint8>::Slice(p + k, n - k)) == n - k } by {
        solve();
    }
}
```

```expect
pass
```
