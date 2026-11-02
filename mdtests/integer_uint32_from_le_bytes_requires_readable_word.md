# The representation lemma grants no read permission

```click
import click::integer;
theorem missing_word(p: uint32*) {
    requires little_endian();
    ensures true by {
        apply(integer::uint32_from_le_bytes(p));
    };
}
```

```expect
fail: required exact fact
```
