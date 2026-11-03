# a primitive type has no structure to induct over

```click
import click::rust::vec;

theorem all_short(v: Vec<uint32>) {
    ensures vec::len(v) < 5u64 by {
        induct(v) as ih {
        }
    }
}
```

```expect
fail: is a Click library primitive type with no constructors
```
