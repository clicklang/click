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

## Checked local-reference endings

`PreparedRustImport::certify_scalar_reference_end` now checks an explicit MIR
borrow/frontier pair against the immutable locked import. Its private
certificate constructor binds the result to the import identity, selected
function and exact MIR points. Function names are indexed once per import;
each query examines only the selected function and continuation.

The supported subset is a mutable scalar reborrow from a local reference,
with the borrow and frontier in one block followed by an acyclic straight-line
continuation. The checker follows copies, reborrows and replacement definitions
from the selected child. It refuses future uses, branches, cycles, aggregate
transport, reference returns and opaque capture, including capture nested in
scalar expressions. Conversions involving a selected alias are conservatively
refused. Storage events never discharge aliases. Reassigning the parent name
does not hide an outstanding child, while replacing a child binding does not
retire copies of the original reference.

The native `set_seven` fixture checks this certificate against actual exported
MIR, checks its import identity and rejects an ending before the child store.
Fourteen bounded unit regressions cover alias copies, storage markers, replacement,
parent reassignment, capture, unsupported paths, call continuations and invalid
points. A deterministic 16/64/256/1024 alias-chain regression bounds work to the
selected input, up to indexing factors. The native fixture also binds its child
store to the exact immutable MIR expression and borrow instance.

The ending certificate now indexes checked scalar memory accesses by MIR point.
Each access retains its read/write kind, per-statement occurrence, reference
local, exact expression, selected borrow point, function and locked import
identity. Copies and direct reborrows retain the original borrow identity;
replacement definitions distinguish a later reference in the same local.
Reborrowing computes an address and is not itself recorded as a scalar read.
Shared aliases may supply read evidence but cannot supply write evidence or
produce a mutable reborrow. A scalar read used to choose another address is
refused as alias transport rather than binding that new address to the original
footprint. A second 16/64/256/1024 regression checks access indexing and lookup.

Locked Rust preparation now carries MIR point, expression-node and reference
identities into typed loads and stores. Lowering indexes only the current
statement's immutable expression nodes, in the same order as the source checker;
it does not use structural expression keys or search other functions.
`CheckedScalarReferenceEnd::bind_executed_accesses` joins its indexed accesses
with completed kernel producer observations from the selected execution. It
checks import identity, function, point, node, reference local and access kind,
then retains the actual pointer and execution alongside the original borrow.

Stores retain source provenance in their existing checked store certificate,
after memory checks succeed. Completed reads retain a private receipt even when
a cached scalar returns without minting a new load variable. Read receipts match
their exact memory snapshot, pointer and type; rewritten facts discard that
provenance. These private consequences are not path selectors. Source-bearing
producer records survive composition as a selected delta, without deduplicating
two operations that happen to have the same semantic memory proposition.
Source metadata remains outside statement/fact comparison and grants no resource
right. Regressions check actual read/write producers, rejection of a different
lock identity, absence of a store observation on a failed write, and distinct
cached reads in one statement.

This read-only certificate proves absence of future selected-reference uses in
that subset. It does not grant memory authority, end a production loan or
change ordinary import/verification acceptance. An unsupported ending query
does not itself reject the Rust program.

## Checked local-reference lifecycle

`src/kernel/loans/local_references.rs` adds the local-reference lifecycle to
the existing immutable `LoanLedger` and its sealed, predecessor-bound checked
transitions. This is a kernel protocol increment; ordinary Rust lowering does
not yet issue these transitions or use their access checks.

Registration checks an exact live owned occurrence for one scalar (`i32`,
`u8`, `u16` or `u32`) and retains its holder, footprint and type. It reserves
one root identity for that occurrence. A reborrow has a fresh reference identity
and the exact parent's shared backing; names and pointer equality cannot
substitute for it. While the child is active, the protocol refuses parent
access, another child from that parent, and parent retirement. Nested borrowing
suspends the intermediate reference too. Independent scalar roots remain usable.

Recovery requires the exact live child, original holder, live ownership support
and absence of a dependent child. It retires that child once and restores its
parent's lifecycle custody. A copied child binding remains expired even after
a new borrow of the same address. Root retirement also waits for its child;
registering the same support afterward creates a fresh identity. Reused checked
transitions require the exact predecessor; altered evidence is refused.

The protocol neither partitions nor mints ownership, stores memory contents,
or rolls memory back. Its access check additionally requires the exact scalar
pointer and type; normal checked memory producers must still establish their
ordinary authority. Whole scalars are the initial subset: aggregate subranges,
fragment joining, shared aliases and call transport need their own integration.
Regression tests cover nested order, copied stale bindings, disjoint roots,
wrong holders/arenas/types/pointers, missing or replaced supports, duplicate
recovery and stale or altered transitions. A test-only invariant walk checks
the dependency/root indexes. Deterministic measurements at 16, 64, 256 and 1024
unrelated roots bound selected lifecycle operations by persistent indexed
lookups; production transitions do not walk the ledger or resource context.

## Executed scalar-reference boundaries

Rust lowering now attaches private source provenance to the assignment for a
direct mutable scalar reborrow. The ordinary assignment producer emits a
private receipt only after successful assignment, checking the actual parent's
pointer before the assignment against the child's pointer and pointer type
afterward. Failed assignments and ordinary untagged pointer copies emit no
borrow receipt. Source provenance stays outside statement/fact comparison;
rewritten facts discard the receipt.

`CheckedScalarReferenceEnd::bind_executed_endings` joins a completed borrow
receipt with a checked child store immediately preceding the selected ending.
It checks the locked import, function, exact MIR points, parent/child source
bindings, indexed store operation and actual pointer. Both receipts must occur
in order on the same execution path. Exactly one matching birth and ending
must exist on that path; repeated observations are refused instead of being
combined across possible dynamic invocations. Endings after other statement
kinds currently have no execution binding. Neither source labels nor a store
without the selected borrow receipt suffice.

These receipts are execution evidence, not recovery rights. They do not yet
carry a local-reference lease or establish a dynamic invocation identity, and
ordinary memory producers still use their existing authority checks. Private
provenance tags remain comparison-neutral; recovery must additionally establish
the selected operation's membership in the locked source plan. Private
receipt deltas retain each producer occurrence without scanning ambient facts;
the existing 16/64/256/1024 regression now also checks borrow receipts.

## Remaining local-reference work

A checked kernel lifecycle does not by itself enforce local references in
ordinary Rust execution. The verifier still must issue births from actual
source execution, preserve reference identity through copies and accesses,
validate the exact ending frontier and invocation, and connect checked
borrow-end frontiers to kernel recovery. Runtime enforcement must also cover
pointer casts, untagged aliases, call transfer and memory havoc. An access observation is not
evidence that every supported ending frontier has executed. The new restricted
boundary binding supplies a completed borrow/store pair, while the ending certificate
alone is insufficient: recovery must also match the source identity, reference
access, borrowed footprint and exact program frontier. Neither last-use guesses nor `StorageDead`
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
cargo test --lib local_reference_
cargo test --lib scalar_reference_
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
