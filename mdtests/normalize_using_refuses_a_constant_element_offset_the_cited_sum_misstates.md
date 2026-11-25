# `normalize using` refuses a constant element offset the cited sum misstates

The constant offset is read as its exact number of elements. A cited sum
with a different constant does not equate the addresses.

```click
import click::integer;

theorem misstated_constant(bytes: uint8[], prefix: uint64, total: uint64) {
    requires to_integer(total) == to_integer(prefix) + 2;
    ensures (bytes + prefix) + 3 == bytes + total by {
        close() using { to_integer(total) == to_integer(prefix) + 2; };
    }
}
```

```expect
fail: `close() using` could not prove the current goal from only its listed premises
```
