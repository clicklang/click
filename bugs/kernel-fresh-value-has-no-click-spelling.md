# A value held in an importer-made local has no Click spelling

Diagnostics print a goal or premise in the sidecar's own terms. When a term
contains a kernel-fresh variable, the value a havoc or a checked operation
introduced, the printer finds no expression that denotes it and prints

```
goal has no exact Click spelling at this frontier
some premises have no exact Click spelling at this frontier
```

in place of the goal and of each such premise.

Seen in the Rust Adler-32 trial after iterator counts became `usize`
(#544). The remainder iterator's count is

```
((len - len % 4) % size) - (((len - len % 4) % size) % 4)
```

where `size` is the kernel variable the lowering's `__rust_checked_94` (the
chunk size, `22208`) holds. Every fact about the count, and about its
`(int32)(uint32)` view, contains that variable. In
`design/charon-trial/adler2/four-byte-compute.click` at the lane loop's
back edge, a wrong arm of `close_invariants by { ... }` reported "goal has
no exact Click spelling" for a member whose only unnamed part was this
variable, and premises about the count were summarised the same way. The
small-batch proof of the same function holds the fact `__rust_checked_94 ==
22208u64` about that local at the same point.

No small reproduction yet. A candidate: a Rust function that iterates
`bytes.chunks_exact(N)` for a `const N`, then the chunk iterator's
`remainder()` by `chunks_exact(4)`, with a deliberately false `have` about
the second iterator's count stated after the first loop.

## Violated invariant

A value that a live local holds has that local as a spelling. A diagnostic
that cannot spell a term says which part it could not name; it does not
drop the whole goal.

## Acceptance criteria

- In the reproduction, the failed goal prints with the local's name in
  place of the kernel variable.
- When a term truly has no spelling, the diagnostic prints the rest of the
  goal with a placeholder for the unnamed part.
- The work spent looking for a spelling of one premise stays bounded as it
  is today; this is about naming a value a local holds, not a wider search.
