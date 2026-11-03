# a proof match on a primitive type is refused

A `Vec<T>` has no constructors, so a proof `match` with no arms does not
cover its values.

```click
import click::rust::vec;

theorem all_short(v: Vec<uint32>) {
    ensures vec::len(v) < 5u64 by {
        match v {
        }
    }
}
```

```expect
fail: match requires a supported datatype with a nonempty constructor family
```
