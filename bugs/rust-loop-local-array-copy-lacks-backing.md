# Rust loop-local array copies lack their backing ownership

## Violated invariant

A plain scalar array created inside an unchanged Rust loop must acquire its
checked local backing before a snapshot copy writes it. It must work when the
sidecar declares only the actual loop-carried resources. Compiler-created
array temporaries must not require users to name them in loop resource clauses.

The arbitrary-head proof of the original locked Adler remainder-vector loop
now passes `U32X4::from` and all four returned lane obligations, then refuses
the copy into `__rust_mir_72` with `missing resource fact owns
__rust_mir_72[0..4]`. The noninductive four-byte proof continues to verify.

## Small reproduction

Use the crate config and sidecar from
`design/charon-trial/chunk-lane-results`. In a separate trial directory, replace
its `quad.rs` with the following source, regenerate the native artifact and
lock with the pinned Charon exporter, and verify its otherwise unchanged
`quad.click` (resolve the config's exporter path to the built Charon binary).
The returned record, byte reads, and loop are the same as the passing fixture;
the additional operation copies its scalar array into a fresh loop-local array.

```rust
pub struct Quad { pub lanes: [u32; 4] }
pub fn load(bytes: &[u8]) -> Quad {
    Quad { lanes: [bytes[0] as u32, bytes[1] as u32,
                   bytes[2] as u32, bytes[3] as u32] }
}
pub fn walk(bytes: &[u8]) -> u32 {
    let iter = bytes.chunks_exact(4);
    for chunk in iter {
        let lanes = load(chunk);
        let array = lanes.lanes;
        let _byte = array[1];
    }
    0
}
```

The proof's `execute_until(assignment(_byte, 0))` fails promptly:

```text
step() could not verify C operation
missing resource fact owns array[0..4]
C operation: write ((UInt32Pointer)array) with 4 scalar elements by snapshot copy
```

Reproduced after the interior base-alias framing fix. Keep this source unchanged
as the regression. Investigate native array `StorageLive`/`StorageDead`, the
entry-hoisted backing, and loop resource reconstruction; the record storage
restart support alone does not supply this array's authority.

## Acceptance criteria

- The reduced crate proves its terminating stored-chunk loop and all lane
  claims with the same loop resource clauses as the passing fixture.
- The original Adler trial advances through its temporary-array copy without
  weakening the array-copy ownership check or adding generated temporaries to
  its loop clauses.
- Empty and repeated iterations handle local storage lifetimes correctly;
  missing backing, wrong extents, stale lifetime evidence, and conflicting
  live loans remain rejected.
- Native source/artifact locking and expanded certificate verification cover
  the repaired operation, with bounded gate tests and indexed state updates.
