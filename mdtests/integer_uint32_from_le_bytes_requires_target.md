# The representation lemma cannot assume a pure theorem's target

```click
import click::integer;
theorem missing_target(p: uint32*) {
    views p[0..1];
    ensures p[0] == p[0] by {
        apply(integer::uint32_from_le_bytes(p));
    };
}
```

```expect
fail: little_endian
```
