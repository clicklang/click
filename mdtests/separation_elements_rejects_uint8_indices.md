# Element separation preserves its supported index types

```click
import click::separation;
theorem unsupported(p: uint8*, i: uint8, j: uint8) {
    requires i != j;
    ensures separate(memory(p[i]), memory(p[j])) by {
        apply(separation::elements(p, i, j)) using { i != j; };
    }
}
```

```expect
fail: elements indices must be int32, int64, or uint64
```
