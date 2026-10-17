# Shared-parent probe: authority control rejects a fact its resource checked

Soundness: not soundness. A program Click verified before is now rejected:
the kernel refuses a checked resource step. No false claim is accepted.

Priority: P2.

On unchanged master `8d8a621c`, the nightly test
`surface::tests::authority_conditional_release_tests::authority_parent_entry_alias_expansion_preserves_later_resource_proof`
fails before it reaches the expansion it tests. It fails while first
verifying the original probe, `design/shared-heap-probes/shared_parent.click`
together with `shared_parent.c`:

```sh
RUST_MIN_STACK=8388608 cargo nextest run --lib --run-ignored only \
  -E 'test(authority_parent_entry_alias_expansion_preserves_later_resource_proof)'
```

```text
the original parent lifecycle verifies: `parent_read_payload.contract` proof
step tactic 3: kernel rejected checked resource `open`: authority control
introduced an unchecked pure fact: ConditionIs(PointerValueEqual(CPointerValue
{ pointer: Pointer { block: ExternalArgument, offset: Int32Scaled { .. } },
designation: Pointer { block: LoadedPointer(..) .. } .. }))
```

The message comes from the introduced-fact check at the end of authority
control construction in `src/kernel/proof/execution.rs`. The rejected fact is
a pointer-value equality that relates an external-argument slot to a loaded
pointer. Merge #1342 changed this test (e7b51a3d, "Find the renamed
shared-parent binder line") only to update the line it looks for. The
verification failure is new since then, or was masked by that lookup.

Invariant: proof steps that verified the probe still verify it. Opening the
`open` resource admits every fact the resource's own checked definition
introduces.

Acceptance: the original probe verifies unchanged, with no changes to its C or
Click source. The nightly test passes, and the cause has a regression in the
gate that keeps the probe's original pattern.
