# Rust borrow authority: production evidence and next protocol

This assessment addresses the borrow-authority requirement in
[rust-support](../issues/rust-support.md). The independently checked checksum
proofs are complete within their published contracts. Borrow authority remains
an architecture requirement, with the following production boundary.

## Current evidence

| Required case | Current evidence | What remains |
| --- | --- | --- |
| Updated child contents return to the parent | Native Rust reborrow, field-guard cleanup and modular owned calls verify through the production engine. | An explicit exclusive-child identity and recovery transition. |
| Parent reuse after the child's last use | `rust_exclusive_reborrow_updates_value_before_parent_reuse_without_child_drop` checks the unchanged `set_seven` witness body, then a real caller. Both contracts expand and reverify. | Connect authority retirement to a supported borrow frontier, rather than assuming local storage end is the borrow end. |
| Disjoint fields remain usable | `rust_owned_disjoint_mutable_fields_verify` checks actual simultaneous field references and updated values; the production call planner partitions exclusive requirements. | Combine footprint partitioning with exclusive child dependencies. |
| Stale child access and duplicate recovery fail | The independent `rust_correspondence_` model checks these cases. Production shared-loan tests check stale bindings and exact recovery. | Corresponding production exclusive-child and submitted-sidecar negatives. |
| Wrong child identity or holder cannot recover | The independent exclusive model checks this; shared production call evidence rejects stale or swapped recovery. | Production exclusive recovery with exact child identity and holder. |

The new native regression deliberately leaves the child reference's storage
alive when the parent is reused. It proves `4 -> 7 -> 8` behavior for the
resource-correspondence helper without requiring an initial value: the child
writes 7 before the parent increments. It rejects final value 7, shared-only
authority for the helper's write, and shared-only authority at the caller.
It checks actual imported helper and caller bodies, not an assumed helper
summary. It does not assert that a stale-child sidecar has been rejected.

In `src/languages/rust/lowering.rs`, scalar `E::Borrow` becomes the address of
the borrowed place cast to the reference's pointer type. Reference declaration
records mutability/type and assigns the pointer; it does not mint an exclusive
child loan. A checked trace of `set_seven` shows `child = value`, `*child = 7`,
and the later load/store through `value`, with no exclusive loan transition.
This is evidence about the current representation, not a reproduced verifier
defect: pinned rustc establishes source borrow legality, while Click checks
functional behavior and memory authority.

Synchronous `owns` calls already reserve exclusive footprints from the caller
and give them to the callee. `plan_stable_view_transfer` reserves these before
planning shared views, records supporting occurrences and retains disjoint
caller resources. This prevents duplicated or overlapping call ownership.
`LoanLedger::reborrow`, however, creates a shared view and pins its parent;
the ledger has no analogous exclusive-child API. A successful native Rust
example therefore cannot close the explicit suspension/recovery requirement.

## Proposed first implementation increment

Use existing synchronous owned-call transfer as the first production boundary
for an explicit exclusive-child protocol. Its entry and return frontiers are
already known, so this increment need not infer Rust nonlexical lifetimes.

1. Bind the reserved owned footprint to a fresh child identity, parent holder,
   child holder and exact supporting occurrence in checked call transfer.
   Keep ordinary disjoint caller resources usable. A nested exclusive child
   pins its parent until the nested return finishes.
2. Validate access against the active child's authority and the exact current
   ledger state. Parent read/write authority over that footprint stays absent
   while the child holds it. Shared-loan rules keep their existing behavior.
3. Consume the child's exact return/recovery evidence once, returning the
   owned footprint with the callee's checked memory result. Do not manufacture
   a value from a separate model or identify recovery by address alone.
4. Exercise the production call path with updated value transport, nested
   children, disjoint fields, wrong holder/identity, duplicate recovery and
   stale child bindings. Preserve ordinary Rust source patterns in frontend
   tests and require expanded-proof agreement. Operations must scale with
   selected transferred resources and relevant ledger changes.

This is a proposed verifier protocol change, not an implemented API. Its
purpose is to connect the explicit model to an existing production transition,
without adding a second execution path. API shape and representation must be
reviewed before implementation. A call-scoped child identity alone will not
close the local-reference requirement: subsequent work must associate local
reference access with authority and establish borrow-end frontiers. In
particular, neither last-use guesses nor `StorageDead` alone may authorize
early recovery, and a live pointer alias must not revive an expired child.

## Reproduce the assessment

With the pinned tools activated and `CLICK_CHARON` set to the pinned exporter:

```sh
cargo test --lib rust_correspondence_
cargo test --lib correspondence_calls_production_
cargo test --test rust_import rust_exclusive_reborrow_updates_value_before_parent_reuse_without_child_drop -- --ignored
cargo test --test rust_import rust_owned_field_parent_can_write_after_explicit_child_drop -- --ignored
cargo test --test rust_import rust_owned_disjoint_mutable_fields_verify -- --ignored
```

The four independent model traces and two production correspondence tests pass;
they establish different claims. The three individually selected native
fixtures cover actual Rust execution and proof checks. No full nightly run is
needed for this assessment. The original
[worked correspondence](rust-resource-correspondence.md) retains its model and
compiler boundaries; this record adds production evidence without treating
compiler rejection as submitted-sidecar rejection.
