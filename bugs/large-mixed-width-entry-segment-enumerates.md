# A large mixed-width entry segment stalls before the proof

Soundness: not soundness. This is a verifier performance defect; no false
acceptance is known.

An empty function with two disjoint owned memory segments should have entry
work independent of their numeric lengths. With a `uint64` segment and a large
`uint8` segment, verification instead stalls before producing a result.

Reproduced on 2026-10-16 in the pointer-subobject worktree, based on upstream
`3e3f5ccd4`, with the compiler exporter rebuilt from that upstream tree:

```c
void entry(unsigned long *word, unsigned char *bytes) {}
```

```click
verifying "entry.c";
void entry(uint64* word, uint8* bytes) {
    owns word[0..1];
    owns bytes[0..2147483647];
} by { execute(); }
```

As an embedded Markdown fixture, `timeout 5 click verify repro.md` exits 124
without a diagnostic. Changing only the byte segment length to `32` verifies
immediately. A larger model-alias/store/call reduction with the same mixed-width
entry pattern consumed 48 CPU seconds without a result before being stopped;
that incomplete diagnostic is not a verification verdict.

`materialize_symbolic_array` in
`src/kernel/functions/globals_and_aggregates.rs` first tries a symbolic run, but
falls back to per-element materialization when its width declaration or run
cannot be admitted. Investigate whether mixed-width declarations on potentially
aliasing parameter addresses force that fallback despite disjoint ownership.
This is a suspected cause, not an established diagnosis.

Acceptance criteria:

- The original two-parameter source and contracts verify promptly at lengths
  32, 1,024, 65,536, and 2,147,483,647 without enumerating the segment.
- Deterministic work regressions show entry work independent of numeric length.
- Overlapping mixed-width reads still preserve correct storage observations;
  the fix must not assume parameter addresses are disjoint without authority.
