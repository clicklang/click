# A Click-typed value reads with its type's methods

A method means what its receiver's type says
(`design/typed-method-resolution.md`). A theorem written in Click syntax
reads a `Slice<uint8>` with the slice's methods, as a Rust sidecar does:
`s.len()` is `slice::len(s)`, `s.as_ptr()` is `slice::as_ptr(s)`, and
`s[1..]` is the subslice, which owes its bounds.

```click
import click::rust::slice;

theorem slice_methods(s: Slice<uint8>) {
    requires 2u64 <= s.len();
    ensures s.len() == slice::len(s) by {
        solve();
    }
    ensures s.as_ptr() == slice::as_ptr(s) by {
        solve();
    }
    ensures s[1..].len() == s.len() - 1u64 by {
        solve();
    }
}
```

```expect
pass
```
