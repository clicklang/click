# P2: Close object-model gaps in supported C++

Priority: P2.

Soundness: soundness-adjacent. Supported access must preserve object type,
initialization, pointer designation and lifetime independently of permission.
The current-master audit below is bounded, not a proof of every admitted path;
no new false acceptance was reproduced. Confirmed false acceptances remain P1
under the repository's soundness policy.

## Goal and current evidence

Make the operations Click already admits compose across calls and resources,
without regressing existing C or Rust. Work from current master, not from the
retired implementation of [PR #646](https://github.com/clicklang/click/pull/646).
The [current-master audit](../design/object-model-current-audit.md) records
source paths, executable witnesses, limits and remaining checks.

Already implemented: pointer subobject bounds and designation, complete pointer
read names, exact construction destinations, initialized/unwritten storage,
initialized output-resource transfer, and the bounded typed/byte representation
rules. These are mechanisms to preserve, not unfinished implementation groups.
The audit distinguishes checked witnesses from broader claims still needing
coverage.

## Remaining work

### 1. Restore the constructed-view getter call

The current-master audit reproduces
`tests/cpp_import.rs::cpp_external_backing_reference_survives_descriptor_destruction_offline`
failing in `run.contract` at tactic 0. A local `View` stores the caller's
pointer; its `get() const` should return a reference to that live backing. The
call is refused before destruction: stable-view planning cannot supply the
loan for `views view[0]`, despite the constructed descriptor and caller's backing
view being present. This is a compatibility failure, not a reproduced false
acceptance or an established failure of lifetime retirement.

- [ ] Reduce the receiver-loan refusal without changing the original C++ or
  weakening its contract, then repair the missing evidence transfer or explain
  the necessary contract correction under current borrowing rules.
- [ ] Restore the original read-only witness, check its writable counterpart
  and hostile contracts, and preserve the existing rejection of references to
  destroyed local backing. Require proof-mode agreement for the repaired path.

The audit contains the exact command and refusal. Do not treat this case as
already supported merely because its regression test exists in nightly.

### 2. Finish the native-interface evidence matrix

For the supported profiles, record what justifies each access at symbolic body
entry and what the actual caller must establish. Cover scalar and record
references/receivers, raw pointers, by-value records, embedded construction,
and pointer/reference results. Use current importer, lowering and shared-kernel
rules; historical archive metadata is not evidence of upstream support.

- [ ] Pair each entry promise with an actual-call positive and rejection
  witness, including subobject bounds, initialized versus unwritten input,
  constness, layout/type and backing lifetime. Credit the existing witnesses
  in the audit before adding tests.
- [ ] Resolve uncovered paths with a checked rule or a specific refusal.
  Establish a concrete admitted source case before changing semantics. A
  signature, byte owner or equal address cannot by itself supply all the
  evidence for access.
- [ ] Publish the resulting supported boundary and assumptions. A separate
  `valid_place` API or the archive's representation is not an acceptance
  requirement; the semantic guarantees are.

### 3. Check modular byte-output composition

The shared `consumes uninitialized(...)` / `produces ...` contract already
expresses body-checked output initialization. Do not rebuild this mechanism.
The selected C++ byte tests separately cover ordinary modular byte writes and
four stores initializing a declared uint32. What remains is their composition:

- [ ] Check a pinned C++ `std::byte*` helper that consumes four unwritten bytes
  and produces them initialized, called with a declared uint32's byte view.
  Prove the exact little-endian word after the modular call.
- [ ] Reject an unwritten byte, missing write permission, a stale observation,
  and a forged byte declaration. Check expansion, cold rewritten verification
  and retained checking for the positive witness.

This small composition is the foundation acceptance case. Bitcoin
`ser_readdata32`, cursor exceptions, broader writable spans and owning containers
belong to [C++ coverage](cpp-support.md); they are not prerequisites for closing
this item.

### 4. Repair pointer-field resource folding and preserve compatibility

The audit also reproduces
[`rb_produces_through_the_root_cell.md`](../mdtests/rb_produces_through_the_root_cell.md)
failing in `rb_set_root.contract` at tactic 4: folding the produced tree needs
a generated equality for `root->rb_node` that has no Surface spelling.

- [ ] Restore that original fixture, retaining a spellable pointer-field
  equality through the store and resource fold. Keep the same C and contract;
  verify the resulting proof across the supported proof modes.
- [ ] Check the affected existing descriptor/resource, pointer-field,
  constructor and cleanup witnesses when delivering a remaining slice.
  Pointer identity, extent and the relevant frame must survive calls, resource
  unfold/refold, branches and loops; unrelated writes must not destroy them.
- [ ] Keep ordinary verification, expansion, cold and retained checking in
  agreement. Use existing deterministic multi-size controls for changed hot
  paths, and the required CI/merge-queue checks for delivery. Do not raise
  budgets or weaken contracts to obtain a pass.

Current rbtree refusals have their own
[launch work](rbtree-example.md) and existing bug reports. Reproduce their
current frontier there before attributing one to the object model. In
particular, the pointer-cell representation repair is implemented but its
[original sidecars still need end-to-end closure](../bugs/pointer-field-cells-are-cached-as-words-a-pointer-read-cannot-use.md).
Historical failure counts are not a current defect list for this item.

## Small intended regression

The modular byte-output witness above must read the exact uint32 after the
helper returns, with no initialization assumed merely from ownership or the
value postcondition. Preserve the original source and contract when reducing
a failure. The existing
[C++ scalar initializer](../mdtests/cpp_initializer_produces_written_memory.md)
and [unwritten-output rejection](../mdtests/produces_refuses_memory_the_function_did_not_write.md)
exercise the shared output-transfer prerequisite.

## Acceptance and scope

Close this item when the two reproduced compatibility failures are resolved,
the interface matrix has named evidence or explicit refusals, the modular
byte-output composition passes its positive and hostile checks, and affected existing C/C++/Rust behavior and proof modes remain checked.
Record any confirmed residual defect at its current reproduction; a missing
coverage check is not itself a demonstrated semantic bug.

Retain typed cells, allocation identities/generations, immutable snapshots and
indexed resource ranges. Keep storage, object/type validity, initialization,
values and access authority distinct. Address equality supports aliasing but
does not manufacture designation. Construction binds the actual destination;
copying does not rebase self-pointers; lifetime end invalidates access to the
backing object. Apply each language's own rules at its frontend boundary.

There is no blanket C++ feature freeze: each new slice must preserve these
invariants and supply its own admission, call and refusal evidence. Broader
lifetime/replacement semantics, union overlap, general inheritance, additional
targets and integer-carried pointer origins are separate coverage work.

The [design record](../design/cpp-object-model.md) preserves the accepted laws
and historical implementation rationale. Recovering the old branch, assigning
all its regressions, reproducing its helper API, or reaching a historical
example count is not a deliverable. History is linked from the current audit.
