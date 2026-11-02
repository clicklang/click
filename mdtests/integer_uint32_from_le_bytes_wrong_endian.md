# The representation lemma requires the stated byte order

```click
import click::integer;
theorem wrong_order(p: uint32*) {
    requires not little_endian();
    views p[0..1];
    ensures true by {
        apply(integer::uint32_from_le_bytes(p));
    };
}
```

```expect
fail: little_endian
```
