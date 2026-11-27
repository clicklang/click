# A library field accessor needs its defining equation

Like a locally defined pure function, `option::unwrap_or` stays folded even
when its argument is a constructor. Expose the defining equation with
`unfold(option::unwrap_or(Option<uint64>::Some(m), d))` before closing the
proof.

```click
import click::rust::option;

theorem an_unwrapped_payload_stays_a_call(m: uint64, d: uint64) {
    ensures option::unwrap_or(Option<uint64>::Some(m), d) == m by {
        close() using {};
    }
}
```

```expect
fail: `close() using` could not prove the current goal from only its listed premises
```
