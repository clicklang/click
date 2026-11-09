# A Vec value reads with its library methods

A library type's methods are its library module's functions over it, so a
`Vec<uint32>` binder reads `v.len()` as `vec::len(v)` and `v[i]` as
`vec::get(v, i)`, as a Rust contract reads a `Vec` parameter. A `let`
binder reads the same way: its type is known when the method is resolved.

```click
import click::rust::vec;

theorem vector_methods(v: Vec<uint32>, x: uint32) {
    requires 1u64 <= v.len();
    ensures v.len() == vec::len(v) by {
        solve();
    }
    ensures v[0u64] == vec::get(v, 0u64) by {
        solve();
    }
    ensures (let w = vec::push(v, x); w.len()) == vec::len(vec::push(v, x)) by {
        solve();
    }
}
```

```expect
pass
```
