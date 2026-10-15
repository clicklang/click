# A refused byte store at index zero reports a four-element range

Soundness: sound. The store is correctly refused; only the diagnostic names
the wrong range, so no false claim verifies.

A function that only views a `uint8` range and stores one byte at `s[0]` is
refused with ``missing resource fact `owns s[0..4]` ``. The store writes one
byte, so the missing authority is `owns s[0]` (one element), which is what
the same refusal reports for a store at `s[2]`. The diagnostic overstates the
footprint by a factor of four, which points a reader at the wrong range when
they repair the contract.

## Reproduction

```c filename=probe.c
void poke(uint8 *s) { s[0] = 7; }
```

```click
verifying "probe.c";

void poke(uint8* s) {
    views s[0..3];
} by {
    execute();
}
```

Observed: `execute()` could not verify C operation: missing resource fact
`owns s[0..4]`. Changing the store to `s[2] = 7;` reports `owns s[2]`. The
same message appears when the bytes are viewed through an opened
`views cstr_at(s, n)` (`mdtests/cstr_at_viewed_string_cannot_be_written.md`,
which matches only the prefix ``missing resource fact `owns s[``).

## Acceptance

- The reproduction is refused with a diagnostic naming the one byte the
  store needs, `owns s[0]`, kept as an mdtest expecting that exact text.
- The `s[2]` variant keeps reporting `owns s[2]`.
