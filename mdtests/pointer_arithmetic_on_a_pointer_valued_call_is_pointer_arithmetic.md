# Pointer arithmetic on a pointer-valued call is pointer arithmetic

A call of a pure function that returns a pointer is a pointer operand, so
`+` on it steps by its result's pointee and a comparison of it keeps its C
meaning. Before, the parser did not know the call returned a pointer and
read the comparison as one of exact Integers, which has no value for a
pointer: the claim was refused as lowering to no path. The same holds for
the method spelling, `s.as_ptr() + k`, and for a literal offset. A generic
axiom may state such arithmetic over its own `T*`, as
`click::rust::chunks_exact` does; it is lowered where it is applied, at a
concrete element type.

```click
import click::rust::slice;

function first(p: uint8*) -> uint8* {
    p
}

theorem offsets(s: Slice<uint8>, t: Slice<uint8>, k: uint64) {
    requires t.as_ptr() == s.as_ptr() + 1;
    ensures slice::as_ptr(s) + k == slice::as_ptr(s) + k by {
        solve();
    }
    ensures slice::as_ptr(t) == slice::as_ptr(s) + 1 by {
        solve();
    }
    ensures s.as_ptr() + k == s.as_ptr() + k by {
        solve();
    }
}

theorem local_pointer_result(p: uint8*, k: uint64) {
    ensures first(p) + k == first(p) + k by {
        solve();
    }
}
```

```expect
pass
```
