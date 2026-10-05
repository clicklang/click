# A native whole-array copy accepts an incomplete source view

## Violated invariant

Copying a whole array requires read authority for every copied element and
write authority for the complete destination. The native Charon proof of
`copy_into` in `examples/rust-array-values/arrays.click` still verifies after
`views source[0..2]` is reduced to `views source[0..1]`, although its unchanged
Rust body copies both elements and its contract observes both results.

This violates the existing regression
`rust_whole_array_copies_require_authority_for_every_element`. Reproduced
independently through the ordinary CLI on
`fe80441b60672facef9d2754f96a351adef4906d` during legacy-retirement testing.
The same original test passed through the legacy exporter before this trial.

## Reproduction

Copy the complete example directory to preserve its locked native inputs,
then change only the source view in the copied Click sidecar:

```sh
cp -r examples/rust-array-values /tmp/charon-array-copy-repro
```

In `/tmp/charon-array-copy-repro/arrays.click`, replace the single
`views source[0..2];` with `views source[0..1];`. Run:

```sh
target/debug/click verify /tmp/charon-array-copy-repro/arrays.click
```

Current result: `16 selected proofs verified` and exit status 0.
Expected result: refuse the full source copy for missing read authority.
The Rust source, config, native artifact, and lock remain unchanged.

The relevant original source and contract are:

```rust
pub fn copy_into(target: &mut [u32; 2], source: &[u32; 2]) {
    *target = *source;
}
```

```click
void copy_into(uint32* target, const uint32* source) {
    owns target[0..2];
    views source[0..1];
    ensures target[0] == old(source[0]);
    ensures target[1] == old(source[1]);
} by { execute(); simp(); }
```

Root cause is not established. Native array lowering uses compact array
region operations. Their evaluator already contains a full-width read check
in `src/kernel/eval/statements/scalar_arrays.rs`; investigate the actual
lowered operation and its resource/loan context before assuming that check
is absent or adding redundant per-element work.

## Intended regression

Run the existing whole-array authority test against freshly extracted native
Charon inputs. Check the valid full view first, then a short source view, a
read-only destination, and a short destination ownership range. Assert that
each negative mutation actually changes the proof text. Include a large-array
scaling case to retain compact work bounds.

## Acceptance criteria

- Full source views and destination ownership verify; incomplete authority
  refuses the operation before its functional postconditions are certified.
- The ordinary prepared API, CLI, profile, expansion, and audit agree.
- Preserve Rust source, original contracts, and bounded compact array behavior.
- The regression runs in the normal gate before legacy extraction is retired.
