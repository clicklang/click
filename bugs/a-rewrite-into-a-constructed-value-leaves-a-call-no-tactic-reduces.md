# A rewrite into a constructed value leaves a call no tactic reduces

Soundness: incomplete. A true goal cannot be closed; nothing false is
accepted.

`slice::len(Slice<uint8>::Slice(p, n)) == n` is proved by `unfold` and
`normalize` when it is stated directly. When the same goal arises from
`rewrite`, replacing a slice variable by its constructor, neither `unfold`
nor `normalize` reduces it, and the diagnostic for the function-proof form
says the goal has "no Click spelling".

Invariant: every goal a proof focuses has a Click spelling that lowers back
to it (`docs/internals/spellability.md`). The written
`slice::len(Slice<uint8>::Slice(p, n))` lowers to the reduced value `n`, so
the unreduced call `rewrite` produced is a goal no spelling denotes, and
`unfold` of the written call does not match it.

## Reproduction

No source file is needed.

```click
import click::rust::slice;

theorem length_after_rewrite(s: Slice<uint8>, p: uint8*, n: uint64) {
    requires s == Slice<uint8>::Slice(p, n);
    ensures slice::len(s) == n by {
        rewrite(s == Slice<uint8>::Slice(p, n));
        unfold(slice::len(Slice<uint8>::Slice(p, n)));
        normalize();
    }
}
```

```text
`normalize` goal did not normalize to true
goal: click::rust::slice::len::<uint8>(Slice<uint8>::Slice(p, n)) == n
```

The control verifies:

```click
import click::rust::slice;

theorem length_direct(p: uint8*, n: uint64) {
    ensures slice::len(Slice<uint8>::Slice(p, n)) == n by {
        unfold(slice::len(Slice<uint8>::Slice(p, n)));
        normalize();
    }
}
```

In a function proof the `unfold` step's trace line is `adds: true`, and a
following `solve()` fails with "could not establish an internal 64-bit
equality goal with no Click spelling". It was met with a library iterator,
after `rewrite(loop(0).iter.as_slice() == Slice<u8>::Slice(bytes,
bytes.len()))`.

## Acceptance criteria

- The reproduction verifies: after the `rewrite`, the goal is the term its
  spelling lowers to, or `unfold` and `normalize` reduce a constructor
  match in the goal as they do in a stated fact.
- An `unfold` whose target does not occur in the goal is refused with a
  message saying so; it does not add `true`.
- No diagnostic reports a goal "with no Click spelling" for this shape.
