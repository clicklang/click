# An unfolded literal argument keeps its own type

Soundness: incomplete. A true claim is refused; nothing false is accepted.

A literal argument takes its parameter's type at the call: `bytes::contains`
takes `lo: uint64`, and `0` passed there is checked as a `uint64`. Unfolding
the call substitutes the literal into the body untyped, so the range
`(lo..hi)` takes `int32` from `0` when `hi` is a `uint64`, and its binder
has the wrong type for the proof that opens it:

```c filename=unfolded_literal.c
int32 unfolded_literal(uint8 p[], int32 n) { return 0; }
```

```click
import click::bytes;

verifying "unfolded_literal.c";

int32 unfolded_literal(uint8 p[], int32 n) {
    requires viewable(p[0..n]);
    requires bytes::contains(p, 0, (uint64) n, 'x');
    ensures bytes::contains(p, 0, (uint64) n, 'x') by {
        execute();
        unfold(bytes::contains);
        obtain (found: uint64) {
            0u64 <= found and found < (uint64) n and p[found] == 'x'
        }
        witness { k: found };
        simp();
    }
}
```

```text
`witness` failed: witness `k` has the wrong type: expected int32, got uint64
```

Writing `0u64` makes it verify
(`mdtests/byte_slice_range_predicates.md`). An unfolded body should read
each argument at its parameter's type, as the call does.

## Acceptance criteria

- Unfolding a call substitutes a literal argument at its parameter's type,
  so the reproduction above verifies with `0`.
- An unfolded non-literal argument whose type differs from its parameter's
  is converted as the call converts it.
- A regression keeps the pattern above, with `0` as the lower bound.
