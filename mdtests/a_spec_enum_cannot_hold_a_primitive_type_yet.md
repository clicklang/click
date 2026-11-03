# a spec enum cannot hold a primitive type yet

```click
import click::rust::vec;

spec enum Batch {
    Of(Vec<uint32>),
}
```

```expect
fail: cannot hold yet
```
