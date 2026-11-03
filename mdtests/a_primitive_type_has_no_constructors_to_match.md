# a primitive type has no constructors to match

A `Vec<T>` has no constructors: neither a written one nor an empty `match`
reads a value out of it.

```click
import click::rust::vec;

function first_or(v: Vec<uint32>, d: uint32) -> uint32 {
    match v {
    }
}
```

```expect
fail: `match` needs a datatype; `Vec` is a Click library primitive type with no constructors
```
