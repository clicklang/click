# A proof trace label reports a snapshot without its origin

Soundness: diagnostic only. The defect is in how `--trace-proof` names the
memory snapshots a trace mentions; it changes no fact, obligation, or verdict.

The label table at the end of a `--trace-proof` report defines each
`snapshot#N` by the construction that produced it. For the multifile-registry
example one label instead reads:

```text
snapshot#2 = INTERNAL ERROR: snapshot constructor did not record its origin
```

The invariant is that every snapshot a trace names has a recorded derivation,
so the legend can say where it came from. The message is the renderer's
fallback (`src/surface/proof_diagnostics/render/legend.rs`) for a memory that
is neither the initial memory nor carries a `derivation()`. Here the snapshot
is the one beneath the seeded initial cells of the global `counters` array,
which the trace otherwise describes as `symbolic storage from snapshot#N`.

## Reproduction

From the repository root, on the unchanged example:

```sh
click verify --trace-proof registry_run examples/multifile-registry/registry.click
```

The proof verifies; the label table contains the `INTERNAL ERROR` line above.

## Acceptance criteria

- The construction that builds this snapshot records its origin, and the
  trace's label table describes it (for example as the symbolic initial
  storage of the program's globals).
- A regression runs `--trace-proof registry_run` on the example, or a reduced
  sidecar with a seeded global struct array, and asserts no label reports
  `INTERNAL ERROR`.
