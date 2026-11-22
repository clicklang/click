# Element separation does not coerce typed indices

```click
import click::separation;
theorem mixed(p: uint8*, i: int32, j: int64) {
    ensures true by {
        apply(separation::separate_elements(p, i, j));
    }
}
```

```expect
fail: type parameter `I` is both int32 and int64
```
