# Rust borrow authority: production evidence and next protocol

This assessment addresses the borrow-authority requirement in
[rust-support](../issues/rust-support.md). The independently checked checksum
proofs are complete within their published contracts. Borrow authority remains
an architecture requirement, with the following production boundary.

## Current evidence after call-scoped integration

| Required case | Current evidence | What remains |
| --- | --- | --- |
| Updated child contents return to the parent | Native Rust reborrow, field-guard cleanup and modular owned calls verify through the production engine. | Synchronous borrowed-memory calls now carry an explicit child receipt; local reference lifetimes remain separate. |
| Parent reuse after the child's last use | `rust_exclusive_reborrow_updates_value_before_parent_reuse_without_child_drop` checks the unchanged `set_seven` witness body, then a real caller. Both contracts expand and reverify. | Connect authority retirement to a supported borrow frontier, rather than assuming local storage end is the borrow end. |
| Disjoint fields remain usable | `rust_owned_disjoint_mutable_fields_verify` checks actual simultaneous field references and updated values; the production call planner partitions exclusive requirements. | Production call receipts now combine nested dependencies with the existing footprint partition; local borrow dependencies remain open. |
| Stale child access and duplicate recovery fail | Production exclusive-call tests reject stale receipts, duplicate returns and missing discharge; native sidecar negatives reject absent write authority. | Local stale-reference access and local recovery remain open. |
| Wrong child identity or holder cannot recover | Production exclusive-call receipt tests reject wrong holders, other call identities, altered supports and a fabricated terminal rollback. | Apply the same requirements to local borrow endings. |

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
the separate exclusive-call receipt now tracks synchronous borrowed memory.
A successful native Rust example alone cannot close local exclusive borrowing: its
reference declarations still create aliases without local child identities.

## Implemented first increment: synchronous borrowed-memory calls

`src/kernel/loans/exclusive_calls.rs` is integrated into the existing call
planner and checked loan-call evidence. It covers `Borrow` requirements over
owned memory. Consumed/moved resources, abstract/composite ownership, and
suspended worker transfers retain their existing protocols.

The planner reserves ownership before issuing a receipt. That receipt binds
one fresh call identity, caller and callee participants, every selected
ownership support (including joined fragments), and the containing exclusive
call when present. The identity is fresh even if a completed call resumes at
the exact original ledger root. A persistent holder index finds the containing
call directly; nested calls increment its dependency count. The outer call
cannot return while a nested child remains active.

Memory authority stays in the existing resource partition. The receipt never
mints an owned fact. The caller residual lacks read/write authority for the
borrowed footprint while retaining disjoint resources; the callee receives
exactly the reserved ownership. Entry and recovery checks validate the live
receipt and its selected supports against that plan. Callee memory updates and
returned contents still come from the ordinary checked call result.

Return requires the exact receipt and original caller, ends the child once,
and releases the parent dependency. Checked evidence rechecks both entry and
return against exact predecessor roots and also requires the receipt to be
closed in the terminal successor. Merely claiming a rollback to an equal
caller root cannot replace child return. Expired receipts, changed supports,
wrong holders, other call identities, missing discharge and duplicate return
are refused. Canonical caller-root restoration remains the existing mechanism;
checked terminal history retains the actual discharge.

Normal kernel regressions cover nested return order, disjoint parent read/write
authority, joined support fragments, move-role separation and forged recovery.
Deterministic persistent-map measurements at 16, 64, 256 and 1024 unrelated
scopes bound a selected entry/return operation by indexed lookup work. Updates
share the selected receipt payload and do not scan unrelated scopes. The
whole-ledger invariant walk is test-only.

The native witness regression now also verifies `nested -> update -> set_seven`,
with a separately owned neighbor set to 9. All three contracts expand and
reverify; false value and missing helper, caller or neighbor write authority
are rejected. This checks actual imported Rust bodies through the same engine.

## Remaining local-reference work

A call-scoped child identity does not close local-reference lifetime handling.
The frontend still must associate local reference access with authority and
establish borrow-end frontiers. Neither last-use guesses nor `StorageDead`
alone may authorize early recovery, and a live pointer alias must not revive
an expired child. Pinned rustc establishes source borrow legality; it does not
replace submitted-sidecar authority checks. No additional source annotation,
separate execution engine or allocation-lifetime authority was introduced.

## Reproduce the assessment

With the pinned tools activated and `CLICK_CHARON` set to the pinned exporter:

```sh
cargo test --lib rust_correspondence_
cargo test --lib correspondence_calls_production_
cargo test --lib exclusive_call_
cargo test --test rust_import rust_exclusive_reborrow_updates_value_before_parent_reuse_without_child_drop -- --ignored
cargo test --test rust_import rust_owned_field_parent_can_write_after_explicit_child_drop -- --ignored
cargo test --test rust_import rust_owned_disjoint_mutable_fields_verify -- --ignored
```

The four independent model traces and two production correspondence tests pass;
they establish different claims. The three individually selected native
fixtures cover actual Rust execution and proof checks; the exclusive-call
regressions exercise the integrated production planner and evidence path. No full nightly run is
needed for this assessment. The original
[worked correspondence](rust-resource-correspondence.md) retains its model and
compiler boundaries; this record adds production evidence without treating
compiler rejection as submitted-sidecar rejection.
