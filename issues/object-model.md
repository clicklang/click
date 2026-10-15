# P2: Stabilize and deliver the shared object model

Priority: P2.

Soundness: soundness-adjacent. This work changes the evidence used to justify
object access, pointer designation, initialization and modular transfer across
C, C++ and Rust. The accumulated implementation has unresolved compatibility
failures and an incomplete admission audit. This issue does not demonstrate a
new false acceptance. Reproduced soundness defects retain their own P1 bugs and
must be repaired or explicitly refused before affected support is claimed.

## Purpose and ownership

Deliver the accepted bounded object model as independently reviewable, green
changes, and recover the oversized work accumulated around
[PR #646](https://github.com/clicklang/click/pull/646). Freeze new C++ feature
admission while establishing this foundation. Completion means a checked model
with demonstrated language boundaries and preserved existing behavior, rather
than an ever-growing collection of successful helper proofs.

This issue owns the shared semantic design, baseline audit, decomposition,
delivery sequence and completion ledger. The detailed laws and operation audit
remain in [C++ object model and shared memory semantics](https://github.com/lacker/click/blob/e3d84a785792c007da19d2f42d75b9e143372164/design/cpp-object-model.md).
[Aggregate construction](../design/aggregate-construction.md) records the
construction/return protocol. Their implementation claims must be checked
against the revision they describe before being presented as upstream behavior.
[cpp-support.md](cpp-support.md) owns subsequent C++ coverage and Bitcoin Core
milestones; [rust-support.md](rust-support.md) owns Rust coverage.

## Recovery starting point

The preserved implementation checkpoint is `b92deef95` on
`codex/cpp-object-model-design`, including upstream `325f9f604`. At that
comparison the branch has 60 branch-only commits and changes 249 files, with
about 62,700 added lines. These measurements describe the local accumulated
branch, not necessarily the head currently published on #646.

The last normal example-project run on this checkpoint passes 35 of 52 projects
and fails 17. Four selected kernel tests, four selected C++ tests and six
Markdown fixtures pass; selected expansion/rewritten/retained checks, Clippy and
documentation checks also pass. These are partial results. No green-tree verdict
has been established for the checkpoint, and its failing projects have not been
systematically classified against the same master baseline. Seventeen projects
are not evidence of seventeen independent defects.

Preserve the full Git history, design decisions and reproductions. Use this
branch as an archive and source of candidate changes. Keep new delivery work in
separate worktrees rooted in an identified upstream revision.

## Accepted semantic design

Retain typed cells, allocation identities, immutable snapshots and indexed
resource ranges. Share operations and checked evidence between execution,
logical observation and modular proofs. Frontends supply explicit language
rules and authenticated source metadata; source spelling or matching numeric
addresses cannot manufacture semantic evidence.

| Component | Required meaning | Independent obligation |
| --- | --- | --- |
| Storage | Allocation identity/generation, live extent and alignment | Existence of an object of the requested type |
| Object and place | Declared/admitted type, containing object, subobject or array domain, lifecycle phase | Initialization and access authority |
| Pointer value | Address plus retained origin/designation, position and relevant lifetime evidence | Permission to read or write its referent |
| Representation | Typed values and byte observations of the same object at a selected snapshot | Legality of every source-language access type |
| Initialization and value | Written/initialized bytes, available value and language-specific value validity | Ownership and a particular asserted value |
| Authority | Checked ownership, view or loan for the actual footprint | Object creation, initialization or pointer origin |

Unknown initialized contents and uninitialized contents remain distinct. Value
forgetting preserves established initialization and object identity; control-flow
joins retain only justified common guarantees. Copying a self-pointer preserves
its original referent. Address equality supports alias and frame reasoning while
remaining separate from complete pointer identity and typed-place validity.

Use shared `valid_place(p)` and `valid_place(p[0..n])` for typed-place validity.
They grant neither ownership nor initialization. `owns` and `views` retain their
access meanings; a view alone does not assert that arbitrary storage contains
an object of a requested type. Initialization effects remain explicit,
body-checked postconditions and transfer separately from ownership and value
claims. Merely mentioning an output read in a proposition cannot initialize it.

Construction uses the exact caller-selected destination. Storage allocation,
construction completion, ordinary value copying and lifetime end are distinct
operations. Construction does not imply freshness or separation. Check the
actual read/write footprints; require padding authority only when the operation
accesses padding. Assignment materializes a separate RHS where the admitted
source semantics require it. Already supported cleanup remains supported.

### Language boundaries

- **C:** retain explicit allocated-storage/effective-access rules and the
  existing verification boundary for ordinary C. C++ object requirements must
  not activate merely because the C frontend knows a struct layout. Preserve
  existing valid C sources and claims, including nullable resource bodies,
  allocation, pointer fields and modular callers.
- **C++:** native references, declarations and checked importer identities can
  supply appropriate place evidence. Preserve phase-specific construction and
  lifetime rules, supported subobjects, bounded copy-equivalent construction
  returns, assignment temporaries and existing RAII/unwind behavior. A native
  signature's promise must be checked at actual calls as well as assumed at
  symbolic body entry.
- **Rust:** reuse shared storage, initialization, representation and transfer
  operations while keeping move availability, drop and borrowing rules explicit.
  Existing fixed-array, iterator, constructor and loan behavior must retain its
  meaning; importing C++ lifetime rules into Rust is not a compatibility fix.

The selected C++ profile remains pinned Clang 19.1.7, C++20,
`x86_64-unknown-linux-gnu`, LP64 and little-endian eight-bit bytes. The bounded
uint32 representation-access guarantee is explicitly an implementation
assumption, identified by `clang19_1_7_lp64_le_declared_uint32_bytes_v1` and
checked in imported artifacts. Authenticate `std::byte` by its pinned
nominal declaration while using native integer contract values. An unrelated
enum with the same width receives no representation-byte privilege.

Keep the approved native cast and shared scalar-initialization semantics.
Their implementation and delivery status belong in the audit; reopen a design
choice only for a concrete contradiction or a newly selected source behavior.

## Audit progress

The [fixed-baseline recovery audit](../design/object-model-recovery-audit.md)
records the immutable comparison, preserved fork archive, commands, dependency
inventory and failure ledger. Master `325f9f604` passes all 52 normal example
projects; a fresh archive run passes 35 and rejects 17 with unchanged source and
contracts. All 17 are branch verification regressions; their introducing changes
and semantic causes still require attribution. The ordinary C scalar-subobject
P1 probe remains incorrectly accepted on both revisions.

The first isolated extraction landed through [PR #926](https://github.com/clicklang/click/pull/926)
in merge commit `16f0d77df`. It preserves captured-pointer pointee types, keeps
missing access authority separate from missing type information, and retains
GNU byte-stride arithmetic for `void*`. All 5,198 selected library tests pass;
required CI and the merge queue passed. PR #646 is closed and its accumulated
implementation and history remain preserved in the fork archive.

The rebuilt fixed master normal gate passes all selected tests, with correct
fixture paths; its cold 20m17s run exceeds the ten-minute budget. The archived
candidate has no full green verdict and fails its normal example stage.

PR [#937](https://github.com/clicklang/click/pull/937) merged the independent
extraction that captures explicit entry reads before placing
them in executable indexed resource bodies. It preserves the selected resource
through the fold and its kernel check, avoiding a second interpretation of the
argument. Plain and nested entry-read positives, wrong-cell controls, and the
existing fieldless entry-argument proof pass. The original C remains unchanged;
the reduced C witness uses existing viewed-range access rather than the
archive's unmerged `valid_place` surface. All 3,758 selected Markdown fixtures,
all-target Clippy and selected expansion/fresh/retained rechecks pass before the
upstream rebase. After rebasing onto `7920aaf0e`, all 52 normal examples, 3,764 Markdown
fixtures, 37 documentation checks, all-target Clippy and the three selected
expansion/fresh/retained checks pass. The first attributed archive group is the
conditional native-composite output check, now locked in by the
[conditional allocated-record regression](../mdtests/conditional_allocated_record_output.md):
a minimal C producer/caller passes on the fixed baseline and fails on the
archive. Repair checkpoint `132cb424b` on the preserved recovery branch restores
allocated-linked-list, heap-object and the reduction. Three targeted kernel
controls and two C++ member-domain rejection fixtures pass. This depends on
archived native-entry machinery and is not an independently landed activation;
its introducing commit still needs attribution.

The next reduced compatibility group is
[native-span output admission for ordinary C buffers](../bugs/native-span-output-loses-c-carrier.md).
Its producer/caller witness passes all four proof modes on the delivered
entry-fold tree and fails on both the frozen archive and the conditional-record
repair checkpoint. Preserve explicit typed validity while repairing automatic
resource annotations and complete-carrier transport. The targeted experiment
restores detachable-buffer and the reduction in all four proof modes; split-buffer
and segmented-buffer still need later range-fold repairs. The repair checkpoint
is `86abef177`; 17 selected kernel controls and the reduced Markdown regression
pass. It remains dependent on archived native-entry machinery. Rechecking all
52 normal examples on `86abef177` yields 38 passing and 14 failing in 71.85s;
exactly the three targeted projects are restored, with no new failing project.
This is not a full green gate.

The next preserved checkpoint, `bd6659d9a`, records an attributed loop escape
repair and the [retained-resource candidate lookup repair](../design/object-model-recovery-audit.md#loop-havoc-borrow-partition-producer-repair).
All 31 selected kernel controls and both C++ member-domain rejection fixtures
pass; eight of nine selected unfold fixtures pass, with the remaining failure
confirmed on the prior checkpoint. The full normal example stage improves to
39/52 passing, with no new failing projects. Concurrency-fork-join is restored
by the escape-only checkpoint and passes all four proof modes. The reduced loop
still needs its later pointer-field range fold repaired; arena still reaches a
control-budget failure. None of these archive-dependent candidates activates
or completes the object model on upstream master.

A focused follow-on reduction on `bcb416098` identifies the later backing-range
fold as another candidate-discovery miss: the memory index selects zero facts,
while the unchanged coverage comparator accepts the held backing owner. Keep
this repair separate from new equality or origin semantics; select checked
producer/frame evidence through an index and retain coverage and withdrawal
controls. The investigation is recorded in the existing retained-resource bug.

The next repair selects a queried pointer read's endpoint through a bounded,
complete-cell certificate and keeps its numeric union local to memory lookup.
A walk stopped at an unproved write retains an opaque read; a cached old value
is not evidence for crossing that write. The selected frame also exposed a
constant-prefix mismatch in signed-order certificate checking, now covered by
positive and withdrawal/reversed-bound controls. This is a shared lookup/checking
repair, not an object-representation change or a new C++ admission boundary.

Recovery checkpoint `53da27b58` repairs the reduced loop's remaining frame gap:
the actual store already carried a checked borrow-partition certificate, but
range disjointness at the loop-havoc summary omitted that producer path. It now
selects the same live loan-bound descriptor view and backing owner through their
indexed address keys and retains the existing full-range/full-width certificate.
All 87 selected controls pass, including a multi-size witness below 200 work
units and width/overlap/ordinary-view/withdrawn-authority rejection controls.
The original loop passes all four proof modes with the safe lookup rule. The
independent exact-arithmetic borrow-frame extraction landed as `3b0550fbc`, using
existing containment and full-access membership. It does not depend on the
archive's broader range-certificate machinery. PR #987 now covers the remaining
full-width explicit-separation repair and indexed candidate selection.

The post-loop-repair example audit at `53da27b58` completes with 39/52 passing
and the same 13 failures as `bd6659d9a`. The next compatibility investigation is
the [reduced modular buffer fold](../bugs/modular-buffer-ranges-fail-to-rejoin.md):
a held prefix and tail use pointer reads from different call snapshots and fail
to rejoin. The identical reduction passes on the upstream-based verifier. Locate
the missing checked frame/transport step before importing broader range rules;
the split-buffer failure needs separate confirmation.

## Recovery and delivery sequence

### 1. Preserve and classify before repairing more examples

- [x] Record the archived branch/commit, published #646 head, fixed master
  baseline, compiler/tool versions and selected fixture/artifact identities.
- [ ] Inventory the accumulated changes by semantic responsibility and
  dependency. Separate proposed laws, implementation, isolated bug fixes,
  importer coverage, tests, documentation and compatibility adaptations.
- [ ] Run the normal gate on the fixed master baseline and the candidate tree
  under comparable conditions. Use the same unchanged programs and claims;
  prepare revision-compatible artifacts from the same pinned inputs when
  schemas differ. Branch-only feature tests are coverage, not baseline regressions.
- [ ] Create a checked failure ledger: test/program, master result, branch
  result, exact command, error/trace, responsible change or smallest reproducer,
  classification, owner and required acceptance checks.
- [ ] Classify each failure as an upstream defect, branch regression, necessary
  semantic narrowing, incorrect fixture/contract, missing selected coverage or
  unresolved evidence. Establish language evidence before claiming source UB.
- [ ] Group demonstrated shared causes and locate the introducing change with
  reduction, selective reversal or bisect in a throwaway worktree. Preserve the
  archive; avoid changing several semantic layers in one debugging experiment.

Normal-gate comparison establishes the baseline. Run only the few affected
nightly fixtures by name; the nightly workflow owns the full nightly suite.
Use unchanged test definitions or comparable source-level probes when tests
moved between gate and nightly. Report timeouts and budget failures as failures.

### 2. Extract the first independently green deliveries

Prioritize reproduced P1 soundness defects, including the
[scalar-subobject pointer defect](../bugs/pointer-arithmetic-crosses-scalar-subobject.md).
Reproduce them on the fixed baseline and the archive before deciding which
activation changes are mandatory. Independent small fixes can land while that
work proceeds, with accurate scope and no claim that the object model is complete.

- [x] Select the smallest useful change that reproduces on the baseline and
  has no dependency on unreviewed object-model activation. Candidate bug fixes
  include captured-pointer pointee typing and alignment-result typing, subject
  to baseline reproduction and current-master status.
- [x] Treat entry-snapshot argument folding as a separate candidate with its
  own dependency check, original-source witness and wrong-cell rejection.
- [x] Extract complete changes with their tests and accurate documentation.
  A historical commit is not automatically a clean semantic unit; reconstruct
  the patch when it combines concerns or depends on later fixes.
- [x] Establish the first replacement's green result and reviewable scope,
  preserve/link the archive, then resolve #646's disposition. Follow the
  repository's one-open-PR-per-task rule: sequential replacements, no stack of
  PRs depending on an unmerged foundation. The completed transition closed
  #646 after preserving the archive and validating #926.
- [x] Use the normal required checks, merge queue and authorized auto-merge for
  the first delivery; verify its final pushed head reached upstream. Continue
  that same procedure for each later slice.

Every implementation slice has a stated invariant, prerequisites, positive and
negative witnesses, appropriate local checks and an explicit supported profile.
Required CI supplies the full gate before merge. Known branch regressions must
be fixed or their introducing change excluded from that slice. A new contract
restriction needs a demonstrated semantic reason and explicit accounting of
compatibility; silently weakening old claims or relabeling failures is not an exit.

### 3. Deliver the shared foundation in dependency order

The following groups are work to account for, not a fixed number of PRs or an
instruction to implement each as one patch. The dependency inventory determines
which parts can land independently and which must form an atomic change.
Credit already landed implementations and existing tests when the audit shows
they satisfy a law. This sequence does not require rebuilding those mechanisms
or migrating all three frontends in one PR.

- [ ] **Operation and evidence audit:** identify storage, layout/type, domain,
  lifecycle, initialization and authority evidence for every admitted operation.
  Audit declarations, construction, copying, moves, typed/byte reads and writes,
  casts, havoc, branch joins, cleanup and lifetime end.
- [ ] **Object/storage and construction:** make layout/subobject evidence,
  destination binding, construction completion and retirement coherent. Preserve
  existing C aggregate returns and Rust construction behavior. Keep bounded C++
  copy-equivalence admission and exact destination checks.
- [ ] **Initialization and observations:** preserve unknown initialized values,
  compressed initialized ranges and explicit output effects. Make the declared
  uint32 typed/byte bridge describe one value at one snapshot; partial writes
  update only their selected bytes and a no-op writer establishes no new output.
- [ ] **Pointer designation and transport:** retain complete pointer evidence
  through address formation, arithmetic, copying, storage/reload, casts, calls,
  resources, substitutions and snapshots. Reject cross-subobject access,
  unjustified array traversal, one-past dereference and expired objects. Address
  observations remain useful without establishing executable typed access.
- [ ] **Entry, resources and modular calls:** assume explicit input promises at
  symbolic entry and check them at actual calls and resource creation. Preserve
  full aggregate/pointer values, selected conditional bodies, mutable descriptor
  entry bindings, returned initialization and the caller's frame. Ordinary C
  metadata must retain its approved compatibility boundary.
- [ ] **Frontend activation:** enable each admitted language/profile only after
  its shared dependencies and positive/negative call controls pass. Unsupported
  cases receive bounded, specific refusals. Existing source profiles must not
  acquire C++ requirements accidentally.
- [ ] **Proof and performance parity:** independently recheck ordinary proofs,
  expansion and rewritten proofs, retained sessions and summaries. Protect local
  operations with deterministic multi-size tests, including growing unrelated
  state. Keep typed cells and intervals compressed; no global environment/history
  scan per step and no raised limits to hide a regression.

Keep reusable inactive machinery behind a checked activation boundary only when
that separation is demonstrably sound. If pointer representation, equality,
transport and access checks depend on one another for soundness, land that
minimal dependency closure together rather than exposing an intermediate model.

### 4. Close compatibility failures and the bounded milestone

The initial ledger must account for these observed groups, without assuming a
cause or that each is introduced by this branch:

| Observed group | Existing reproduction or check |
| --- | --- |
| Pointer-field frames and stored values | [C frame bug](https://github.com/lacker/click/blob/e3d84a785792c007da19d2f42d75b9e143372164/bugs/c-pointer-field-postconditions-lose-frame-evidence.md); original owned-vector and owned-string projects |
| Nullable allocated resource bodies | [Conditional allocated-record regression](../mdtests/conditional_allocated_record_output.md); original allocated-linked-list and heap-object projects |
| Borrowed/owned buffer and cursor transfer | Original arena, detachable-buffer, owned-segmented-buffer, owned-split-buffer, input-cursor, binary-tree, concurrency-fork-join, multifile-registry and ring-buffer projects |
| Other C proof failures after upstream integration | Original refcount and rbtree-augmented projects |
| Rust availability/ranges and proof cost | Original rust-chunks-exact and rust-byte-sum projects |
| Importer and proof scaling | Existing record-inventory multi-size work assertion, growing-place graph test and affected decoder audits |

- [ ] Give every observed failure a baseline classification and resolve each
  regression attributable to the delivered slices. File reproduced defects in
  `bugs/` and remove their files once fixes, regressions and documentation land.
- [ ] Complete the [bounded acceptance matrix](https://github.com/lacker/click/blob/e3d84a785792c007da19d2f42d75b9e143372164/design/cpp-object-model.md#stabilization-work-and-exit-criteria)
  with named evidence: representation, modular transfer, destination/copy,
  aliasing/frames, lifetime/availability, typed access, proof modes and scaling.
- [ ] Verify the unchanged pinned Bitcoin `ser_readdata32` source and helper
  with exact word value, initialization, span bounds and backing-lifetime claims,
  including modular, expanded and retained checks. Its already passing local
  proof is an acceptance witness, not a substitute for shared compatibility.
- [ ] Record which invariants and fixtures landed in which upstream commits,
  remove resolved bug documents, reconcile implementation claims in the design,
  and move the next C++ feature work back to `cpp-support.md`.

## Small intended regression

Use the existing [entry-count cell fixture](../mdtests/resource_uint64_entry_cell_fold.md):

```c
int32 probe(int32* p, uint64* count, int32 input) {
    *count = *count - 1;
    p[*count] = input;
    return input;
}
```

Its resource owns the original last cell, with the backing pointer and original
count captured at entry. Decreasing the descriptor must not move the ownership
promise to a different cell. The proof unfolds, executes and folds using the
entry count. The [wrong-index counterpart](../mdtests/resource_uint64_entry_cell_fold_wrong_index.md)
must fail, and a view-only counterpart must reject the write. These fixtures
exercise a shared operation with ordinary C before relying on the C++ span
adapter. Reuse existing C++ span/caller and Rust range tests for their distinct
language boundaries; do not manufacture duplicate coverage for the checklist.

## Scope and design decisions still requiring evidence

Placement construction/storage reuse, overlapping unions, general inheritance
and virtual dispatch, broader exceptional construction, arbitrary owning
containers, concurrency and additional target profiles remain outside this
bounded milestone. Full contracts for integer-carried pointer origins remain
in the separately requested P2 [origin-contract issue](https://github.com/lacker/click/blob/e3d84a785792c007da19d2f42d75b9e143372164/issues/integer-pointer-origin-contracts-design.md),
including its provisional `pointer_origin` predicate and specific rejection
controls. They are not prerequisites for merging unrelated green slices.

Implementation structure and extraction order are engineering work. Ask for a
new design decision when a concrete case would change an accepted source-language
promise, choose a new compiler guarantee or contract surface, or enlarge this
bounded profile. Do not reopen the model merely because a proof is difficult.
Trace presentation changes continue to follow `AGENTS.md` approval requirements.

This issue is complete when the bounded laws and audited activation have landed,
introduced regressions are closed, the acceptance evidence and supported limits
are documented, and remaining excluded features belong to their existing
roadmaps. Preserve durable design and delivery records, then delete this issue
under the normal issue lifecycle.

### Buffer-join recovery checkpoint

`477784302` preserves the selected supplier-coordinate repair described in the
[recovery audit](../design/object-model-recovery-audit.md#checked-coordinate-buffer-join-repair).
Both original buffer pipelines and the reduction pass all four proof modes;
86 selected kernel controls pass. The example stage improves to 41/52 with no
new failures. This supersedes the earlier unconfirmed split-buffer attribution.
Next assess an independent upstream extraction, then reduce the remaining eleven
compatibility failures. Do not activate the archive as a whole.

The supplier-coordinate extraction landed in PR #1011. Recovery checkpoint
`c6d5c4200` additionally checks registered read prefixes during interior-write
lookup (87 selected kernel controls passing). This is partial progress: the
[two-store execution reduction](../mdtests/pointer_field_reloaded_backing_writes.md)
still fails, as do the original string/vector postconditions. Continue there;
keep the 41/52 audit count until a new complete example run establishes otherwise.


`a1cf07a24` closes that two-write execution gap using scoped certified read
bindings, including retained-session checking, without publishing their value
bridges to sibling contexts. The positive regression passes all four proof
modes; 133 selected recovery controls pass. Continue with the
[string/vector postcondition gap](../bugs/c-pointer-field-postconditions-lose-frame-evidence.md),
keeping C and claims intact and distinguishing an explicit checked equality
proof from `assumption`'s exact-fact lookup. The full example audit remains 41/52.

The next proof-only slice supplies explicit checked stored-value equalities in
`owned_string_set` and `vector_push`; their original function contracts now
verify. Continue with string push's terminator comparison and the later vector
allocation fold. This does not close either complete project or change the
41/52 archive audit. See the
[focused evidence](../design/object-model-recovery-audit.md#explicit-stored-value-proofs-in-the-original-examples).


Upstream now verifies both full string/vector projects after the focused
string-push proof adjustment. The remaining string pointer-frame and vector
allocation-fold failures are specific to the recovery archive; continue reducing
those compatibility obligations before activation. See the
[upstream/archive distinction](../design/object-model-recovery-audit.md#string-push-proof-and-full-upstream-project-checks).

The split-field string fold now passes at unchanged limits after the
[preliminary byte-gap query repair](../design/object-model-recovery-audit.md#preliminary-byte-gap-query-repair).
The focused archive proof passes fresh, expanded, rewritten and retained checks.
The archive's clear proof now also passes, and the full original string project
passes all four modes. The completed archive audit improves to 42/52; ten
compatibility failures remain. Continue reducing the vector allocation fold
across its modular push call, using the existing checked pointer-field effects
before considering any new contract surface. The graph-lock follow-up passes
all 5,415 current-upstream normal library tests and 168 C++ import/span tests.
Keep the original C, split-field resources and contracts intact; the separate
returned-resource performance report is not closed by the fold repair.


PR #1054 has merged; both pushed trace-fix commits `7350af8a0` and `09c1cf285`
are verified upstream. The latest archive audit after the selected read-frame
repair remains 42/52 with no new failures. Continue the
[selected resource-delta extraction](../design/object-model-recovery-audit.md#selected-complete-read-bridge-for-resource-deltas)
and the separate full-pointer evidence gap at the vector allocation fold.


The checked-spelling extraction landed in PR #1081; both pushed commits
`346b87a69` and `76b262027` are verified upstream. Its final correction keeps
normalized lookup spellings separate from authored certificate forms. All 52
normal upstream example projects and 46 normal fixed-state controls pass, as
does library Clippy with warnings denied. The original recovery vector remains
incomplete: its explicit prefix proof still exhausts the unchanged control
budget inside preliminary cross-snapshot availability lookup.

The cursor reduction exposes a separate C pointer-field initialization gap.
An opaque full pointer value must retain its identity through a checked copy
without acquiring native type, lifetime, initialization, or access authority.
Use the existing unresolved-value representation; do not infer a native record
from C layout or replace full-value equality with address equality. Continue
with independently checked field-copy effects and their modular output
transfer. No new archive audit has run; retain 42/52 and the same ten failures.


Recovery checkpoint `d06045be7` retains canonical opaque C pointer inputs
without importing caller cells or object authority. All five independent-entry
controls pass, including multiple unrelated-state sizes and forged-identity
rejections. The broader pointer selection has 472 passes, three failures and
17 ignored controls; a baseline run on `2cab205db` has the same three failures
(471 passes). Keep untyped-pointer error classification, pointer-field
address-equality rejection, and modular record-pointer identity return on the
activation checklist. The existing scalar-subobject bug records the archive's
still-accepted pointer-field countermodel. No complete cursor proof or new full
archive audit is claimed.


Recovery checkpoint `2dc992cfe` closes the cursor initializer's modular
returned-view gap. It preserves opaque copy operands as values without native
input promises, reproduces declared read-only input projections independently,
and restores certified input-field copies before returned-view matching. The
original initializer C, resource and contract are retained in
`mdtests/c_pointer_field_copy_preserves_borrowed_view_across_call.md`; its caller
passes fresh, expanded, rewritten and retained checks on both recovery and
current upstream. This fixture is an independent compatibility control, not
activation of the recovery object model.

The archive's original shared pipeline passes both initializer calls and now
fails at `input_cursor_take`, whose returned borrowing composite still observes
a fresh pointer. Continue its field-preservation summary separately. Six entry
and seven field controls pass; the broader pointer selection has 477 passes,
two known failures and 17 ignored controls. Those failures remain the loaded
field/address-equality rejection and modular declared-record identity return.
The last full archive example audit is still 42/52.

The next recovery audit on archive checkpoint `07d355f0e` still passes 42/52,
but with a changed failure set: input-cursor and binary-tree are restored,
while borrowed-slice and perpetual-service newly fail. The remaining eight
failures are arena, multifile-registry, owned-vector, rbtree-augmented, refcount,
ring-buffer, rust-byte-sum and rust-chunks-exact. Do not treat the unchanged
total as evidence that the latest archived copy-transfer work is compatible.

The service failure has a focused upstream control in
`mdtests/c_owned_pointer_resource_modular_loop.md`, preserving the original
step, loop, resource and contracts. It passes on upstream-based `2c484f457`;
the original service loop also passes fresh, expanded, rewritten and retained
checking on that tree. The archive learns a C-allocated typed-prefix access
witness during the call and incorrectly counts it as an allocation-lifetime
change. Its repair must keep physical allocations and native object promises
strict while distinguishing C access knowledge. Borrowed-slice separately
requires write authorization from the call's already checked mutable resource
projection. These repairs are recovery work, not upstream feature activation;
repeat the complete archive example audit before reporting a new count.

Recovery checkpoint `f936e47d8` repairs both regressions. The normal example audit
now passes **44/52** in 105.27 seconds, with exactly the other eight failures
listed above and no new failing project. The original service loop passes all
four proof modes; its focused Markdown control passes on both trees. All 22
native-input controls pass. The broader pointer selection has 477 passes, the
same two documented failures and 17 ignored controls. These are preserved
archive results, not an upstream activation or full green-gate verdict.

The narrower cursor-take caller recorded in the carrier bug also fails on
upstream-based `2c484f457`, for missing borrowing-composite loan backing. Keep
that baseline limitation separate from archive compatibility regressions;
the original input-cursor project is restored on the recovery branch.

The ring-buffer regression is repaired in recovery checkpoint `9d2c9dbc4` by
freezing one load-naming snapshot across each composite body unfold/open.
Later clauses still lower their selectors through earlier cached fields, but
cached reads no longer create a new naming epoch. This is the existing body
instantiation rule, applied consistently; the kernel acceptance rule, object
representation, original C, contracts and resources are unchanged.

The original ring-buffer pipeline and its nested-resource reduction pass all
four proof modes on the archive. The reduction also passes all four modes on
the upstream-based tree. The new nested-resource fixture and existing resource
unfold/child-overwrite controls pass upstream. On the archive, eight of nine
existing resource-unfold fixtures pass; the unmatched-body fixture's later
loop-exit fold failure is also reproduced with the prior `f936e47d8` executable.

The full normal recovery audit now passes **45/52** in 109.05 seconds,
restoring ring-buffer with no new failure. Remaining projects: arena,
multifile-registry, owned-vector, rbtree-augmented, refcount, rust-byte-sum and
rust-chunks-exact. No full green-gate or native-feature activation is claimed.

Recovery checkpoint `0822e0f20` restores multifile-registry by completing an
incomplete global array's executable row metadata from the compatible linked
definition. Scalar type, rank and inner dimensions must match; source-resolved
shadowing locals retain their own shapes. The kernel's strict shape checks are
unchanged. Shared immutable/mutable exhaustive C AST child walks keep this
source preparation linear in visited syntax with indexed declaration lookups.
Three new completion controls, ten addressability controls and eleven selected
array-row controls pass on the archive, including ambient-global scaling and
existing strict shape rejections.

The new upstream controls cover the extern reader, a shadowing local and an
out-of-bounds row. All three pass on both trees; master refuses the last case
for missing read authority and the archive rejects the invalid row before
access. The two positive controls pass fresh, expanded, rewritten and retained
checking upstream; the original registry result proof passes all four modes on
the archive and all five original project proofs verify. The normal archive
audit is **46/52** in 106.44 seconds, with no new failing project. The six
remaining failures are arena, owned-vector, rbtree-augmented, refcount,
rust-byte-sum and rust-chunks-exact. No full green gate or activation is claimed.

The separate archive trace defect is preserved in
[the refcount trace reproduction](https://github.com/lacker/click/blob/db1cc4541/bugs/archive-refcount-failure-loses-proof-trace.md).
Its original post-call pure comparison loses the checked trace prefix; investigate
that recording defect before guessing at its missing count relation.

The refcount trace defect also reproduces upstream with a minimal false
`have x == 2 by auto` after a helper proved `x == 1`. The early source-have
refusal dropped the checked proof's diagnostic provider. Attaching the same
provider used by its other refusal paths preserves the existing message and
restores the checked trace prefix; failed smart candidates add no facts.
The new regression and all 73 active diagnostic controls pass (nine ignored).
On the archive, the original refcount trace now records the post-retain read
equal to `1 + amount`; its functional failure still needs diagnosis. Retain
the 46/52 audit count.

The shared diagnostic repair landed through
[PR #1131](https://github.com/clicklang/click/pull/1131), with its pushed commit
verified on upstream. The restored refcount trace showed the same read in the
goal and the `1 + amount` value fact, together with its bounds and overflow
premise. Rewriting that value and invoking arithmetic with the existing
premises completes the comparison. The original C, contracts and resources
remain unchanged. The explicit pipeline proof passes fresh, expanded,
rewritten and retained checking on both the archive and upstream-based
`3c616ce13` tree.

Recovery checkpoint `cb6c3772c` restores refcount. The full normal archive audit
now passes **47/52** in 146.33 seconds, with no new failing project. The five
remaining failures are arena, owned-vector, rbtree-augmented, rust-byte-sum and
rust-chunks-exact. Concurrent local compilation affected this run's elapsed
time. The archive's trace bug file is closed; its historical reproduction at
the immutable link above remains available. This is not a full green gate or
native-feature activation.

Refcount delivery [PR #1136](https://github.com/clicklang/click/pull/1136)
merged; both pushed commits are verified on upstream. The next shared repair
recognizes cached function-pointer values in definitional memory comparison:
the canonical representation names an exact registered load at zero offset,
which the existing comparison did not recognize. The read must still have the
cell's load kind, read that cell and be unchanged across snapshots. The kernel
regression reproduces upstream before the fix; controls reject a different
cell, narrower load, arbitrary symbol, displacement and changed cell value.

On the recovery archive, that repair gets past the original red-black tree
callback `open`. Explicit references to the callee's existing result and
inorder facts complete the entry-module proofs without changing C or contracts.
The normal archive audit is **48/52** in 111.13 seconds; remaining failures are
arena, owned-vector, rust-byte-sum and rust-chunks-exact. This is the normal
entry-module audit under conditional imported interfaces, not proof of every
imported helper. Selected proof-unit checking additionally reaches the known
integer-to-pointer origin refusal in an imported rotation helper. No full green
gate or native-feature activation is claimed.

Byte-sum's two exhausted smart searches are now explicit applications of the
existing integer-conversion lemmas and arithmetic over relevant premises.
Original Rust and contracts are unchanged. Its result proof passes fresh,
expanded, rewritten and retained checking on both the archive and this
upstream-based branch. The last complete archive audit remains **48/52**;
byte-sum is individually restored pending the next complete audit.
