# A library field function of a constructed value is not its field unopened

`option::unwrap_or(Option<uint64>::Some(m), d)` lowers as the call that was
written. Proving `option::unwrap_or(Option<uint64>::Some(m), d) == m`
requires exposing the definition with `unfold`.

```click
import click::rust::option;

theorem unopened(m: uint64, d: uint64) {
    ensures option::unwrap_or(Option<uint64>::Some(m), d) == m by {
        close() using {};
    }
}
```

```expect
fail: `close() using` could not prove the current goal from only its listed premises
```
