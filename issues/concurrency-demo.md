# P1: Verify representative concurrent C programs

## Goal

Verify ordinary concurrent C through composable resource contracts. Built-in
memory and mutex resources should obey the same ownership and transfer rules
as user-defined resources wherever possible. Keep the C fixed when proof work
exposes a verifier gap.

The launch milestone remains three programs: disjoint fork/join workers,
mutex-protected shared mutation with an exact result, and one-shot
release/acquire publication. The parity loop is a completed intermediate
mutex milestone. Safety must cover arbitrary compatible schedules, including
execution prefixes that never complete. Exact results are conditional on the
relevant operations completing; they do not establish fairness, deadlock
freedom, or termination of polling.

## Population semantics

The authority migration is complete. Populations use explicit `authority(...)`: a control
owns the authority, a mutex protects the control, and workers follow the
[worker authority protocol](../docs/internals/worker-authority-protocol.md).
`examples/shared-refcount/` is the mutex-protected shared-refcount acceptance
example, and `guarded_by` is retired. This issue states the remaining
concurrency scope.

The [contract and diagnostics record](../docs/internals/concurrency-contracts-and-diagnostics.md),
[mutex contract design](../docs/internals/mutex-resource-contracts.md), and
[resource-argument record](../docs/internals/resource-parameters.md) contain
historical checkpoints.

## Current state

| Demonstration | Verified today | Still missing |
| --- | --- | --- |
| [Disjoint fork/join](../examples/concurrency-fork-join/fork_join.click) | Exact outputs, ownership transfer, stable input loans, matching joins, and create-failure cleanup | Native runtime validation and broader threading APIs |
| [Even/odd locking](../design/concurrency-probes/mutex_held_parity.click) | Conditional acquisition across loop iterations, final unlock, and destruction | The conditional acquisition abstraction with protected payloads or use-loan-backed guards |
| [Shared-worker counter](../design/concurrency-probes/mutex_counter.click) | Worker and parent safety, shared typed use permissions, create-failure cleanup, final destruction, and the exact final value of two | Nothing for the frozen C |
| One-shot publication | Design obligation only | Checked release/acquire semantics and a frozen C demonstration |

The parity loop works both through an ordinary conditional guard resource and
[direct conditional ownership in its loop contract](../design/concurrency-probes/mutex_held_parity_direct.click).
`loop_guard` is an example resource name, not a built-in construct.

The counter's typed use permissions identify the protected resource. Successful
creation transfers a checked worker share while retaining a parent share;
failure leaves authority unchanged. Joins recover shares into the current
ledger in either order. Destruction requires complete recovery. Shared
acquisition and release forget observations consistently with interference;
completed workers alone do not establish the final counter value. The control
the mutex protects owns the counter with the authorities for contributions and
credits, and its facts tie the counter to the contribution count, so the parent
reads exactly two after both joins and destruction.

Mutex initialization checks writable storage and alignment. Initialized bytes
are reserved against ordinary writes, and live mutexes prevent overlapping
free/realloc and automatic-storage expiry. Initialization identities distinguish
destruction and reinitialization at the same address. Named authority binders,
preserving helpers, balanced use helpers, typed lock/unlock payload transport,
and same-thread acquiring/releasing helpers are implemented. These are
supported subsets, not general lifecycle-consuming/producing contracts.

All these client proofs use the explicitly selected
[modeled pthread specification](../src/languages/c/modeled_pthread_spec.md).
They do not validate a native pthread implementation. A locked Ubuntu
GCC/glibc import verifies through the ordinary import path, including on
macOS; that is an artifact and declaration-identity regression, not a native
runtime guarantee.

Local mutexes protect a population's control, which owns the counter and the
authority. The [held-helper test](../mdtests/population_mutex_helper_held.md)
verifies; the [unheld-helper test](../mdtests/population_mutex_helper_unheld.md)
requires `owns mutex_guard(&p->mutex)`. Members held outside the mutex grant no
access to the counter while it is unlocked.

### Mutex model boundary

A successful acquisition supplies a unique owned guard and resources satisfying
the protected assertion. Unlock requires that acquisition and an owned,
restored assertion; restoring it may use a replacement resource instance and
new field values. An old local value remains a fact about that local value,
not evidence of the current protected memory after interference.

The independently checked typed-use path currently requires an unconditional,
field-bearing leaf resource with a memory footprint independent of changing
model fields. It rejects recursive or matched bodies, named child resources,
existential pointer witnesses, and resource-reference parameters. Flat abstract
tokens, including symbolic quantities, can be ingredients of that resource.
The conditional loop acquisition abstraction requires an empty mutex, locally
owned lifetime authority, and no use hold.

[Acquiring/releasing helpers](../mdtests/mutex_helper_transfers.md) use ordinary
`owns`, `consumes`, and `produces` clauses and named call maps. The supported
subset has one named preserved use input, a produced or consumed guard, and a
matching protected-state transfer for typed use. Nested synchronous wrappers
retain the exact acquisition and lifetime dependency. Viewed or conditional
clauses, additional protocol transfers, and lifecycle-changing helpers remain
outside this subset. Unary transfer helpers require a payload-free protocol.

## Surface language decisions

Keep the existing ownership vocabulary: `owns`, `views`, `consumes`, and
`produces`. Resource fields, facts, quantities, conditional bodies, and
fold/unfold remain general resource features. Sequential, lock-protected, and
atomic access are semantic disciplines, not three new declaration keywords.

| Spelling | Role | Decision |
| --- | --- | --- |
| `mutex_live(mu)` | Lifecycle authority for one initialization | Keep distinct from use and acquisition |
| `mutex_use(mu)` | Permission to participate while lifetime is guaranteed | Keep; unary use does not expose a guessed payload |
| `mutex_use(mu, counter_state(p))` | Use authority with an authenticated protected resource type | Keep the accepted shape; generalize only when a concrete ordinary-resource example needs it |
| `mutex_guard(mu)` | Exclusive ownership of an acquisition | Keep |
| `guarded_by p->mutex;` | Retired; refused with a diagnostic | Associations come from initialization and ordinary transfer |
| `held(mu)` | Checked fact about the current path's acquisition | Convenience predicate; never a substitute for owned guard authority |
| `runtime "modeled-pthread";` | Explicit selection of the trusted runtime specification | Keep the assumption visible |

`access`, `guard`, `state`, and `lifetime` are runtime contract binder names,
not ownership keywords. `storage` is a planned binder for ordinary memory,
not a new resource family. Runtime named storage transfer and destruction's
named state output are not yet implemented, although concrete destruction
recovers protected state.

Do not introduce angle-bracket resource parameters, a `protecting` modifier,
a `uses` clause, or public acquisition/continuity identifiers. Existing
algebraic type applications such as `List<int32>` are unrelated to this
restriction. `authority(...)` is the population interface. The old
`count_authority`/`create_count` and sum-specific interfaces remain superseded
proposals, and `guarded_by` is retired rather than extended to more
mutex-address forms. Initialization association, owned-state checks, and
stale-initialization rejection remain required.

## Relationship to Iris

Use the [Iris lock interface](https://plv.mpi-sws.org/coqdoc/iris/iris.heap_lang.lib.lock.html)
as the ownership reference: initialization deposits an assertion, acquisition
returns an exclusive lock token and that assertion, and release consumes the
token and the restored assertion. Click follows this discipline, but does not
thereby implement Iris or inherit its soundness proof.

Iris's basic lock description is persistent and its invariant can be an
arbitrary logical assertion. Click tracks use loans to support C destruction
and storage reclamation, and currently accepts much narrower protected
resources. The basic Iris interface does not include destruction. These are
explicit differences, not grounds for treating use authority as a stable view
of mutable payload.

Exact concurrent results need a checked relation between resources held by
workers and state protected by the invariant. The authority migration specifies
that relation and its permitted updates. Similarity to Iris's lock interface
alone does not establish population conservation or exact totals.

## Ordered implementation plan after authority migration

### 1. Complete the mutex-protected counter

Complete. The unchanged [counter C](../design/concurrency-probes/mutex_counter.c)
verifies at exactly two when both workers are created and joined, with safety
and cleanup on both create-failure paths. Each worker spends a credit and
creates a contribution under the lock; the parent receives both authorities
with empty populations through its contract, because the counter is caller
storage. `mdtests/mutex_counter_*_rejected.md` refuse a wrong increment, a
fabricated credit, a doubled contribution, and a total observed before the
second join. The
[missing-conservation regression](../mdtests/mutex_resource_quantity_requires_conservation.md)
remains.

### 2. Test protected-resource composition

Authority nested inside an ordinary protected control resource is exercised by
the prerequisite migration. Extend that support with an ordinary named child
and a protected ownership footprint that changes, such as an allocated
collection growing while locked. Freeze the C before adapting the verifier;
do not flatten source or resources to fit a leaf restriction.

Use these examples to determine needed support for recursive assertions,
changing footprints, and payload-bearing conditional loop guards. Extend
ordinary resource reasoning rather than adding a mutex-specific assertion
language. Retain the parity loop and both forms of its guard contract.

### 3. Review the contracts actually used

Compare the helper, counter, shared-refcount, and composition proofs with the
implemented interfaces. Keep `owns`/`views`/`consumes`/`produces` and precise
missing-fact/resource diagnostics. Removal of `guarded_by` is already decided
and belongs to the prerequisite; do not reopen it as an undecided feature.

The abandoned resource-description parameter scaffolding has been removed;
`<P: Resource>` was never accepted. Keep useful implemented named
resource-reference arguments, whose values select owned occurrences. General
resource-type parameters remain deferred unless an example requires them.
Disabled runtime binder projections remain unfinished, not implicitly accepted.

Acquiring/releasing helpers already work for the named subset described above.
Maintain checks against fabricated guards, replacement of preserved acquisitions,
release without restored state, and destruction with surviving loans or guards.
Do not move pthread guards across threads. Direct `pthread_mutex_t *` sidecar
parameters remain a separate parser limitation with a frozen negative test.

One-shot publication is the next launch milestone; it is not part of the
authority migration's initial implementation scope.

## Remaining launch obligations

### One-shot release/acquire publication

Freeze a C11 producer/consumer example. The producer initializes ordinary
payload and release-stores a ready flag; the consumer acquire-loads the flag
and reads only after observing publication. Prove the initialized value is
observed without requiring the polling loop to terminate.

Tie the acquire observation to the actual release and its resource transfer.
Transfer exclusive payload authority at most once; repeated observations and
competing consumers cannot duplicate it. Reject reads before publication,
producer accesses after surrendering ownership, and proofs with a required
ordering edge weakened to relaxed. Unsupported orders must be refused locally,
not silently strengthened.

### Native pthread binding

For any native execution claim, bind the selected declarations, ABI, compile
options, and runtime semantics to a pinned platform profile. The first intended
profile remains Debian Bookworm GCC 12/glibc 2.36, C11, x86-64 Linux user space,
LP64, as recorded in the [probe record](../design/concurrency-probes/README.md).
The existing Ubuntu GCC 13/glibc 2.39 artifact does not validate that profile.
A macOS claim needs its own binding and artifact identity.

Reject mismatched headers, types, options, and same-named lookalike functions.
Keep client proof completion separate from native runtime validation. The
[binding design](../design/concurrency-probes/pthread-binding-design.md) records
the present boundary.

## Diagnostics and proof obligations

Failures should identify the missing fact or resource in Click terms, such as
`Requires owns mutex_guard(mu)` or `Requires owns counter_state(p)`. A failed
body fact should identify the actual proposition, rather than only a body-clause
number. Association mismatches should show the required and supplied resource
types. Distinguish unsupported forms from missing premises; do not disguise an
implementation restriction as a fact the user ought to prove.

The kernel must check ownership conservation, initialization and acquisition
identity, lifetime dependencies, synchronization, and permitted interference.
Stable `views` freeze their memory and cannot authorize reads of concurrently
changing payload. A matching join recovers one child's checked outputs once;
a saved worker or parent snapshot cannot replace the current shared ledger.

Preserve historical facts while requiring current authority for current-memory
claims. Keep protocol generations and acquisition identities internal. All
rules must remain sound under arbitrary compatible threads, not one convenient
schedule. Proof tactics may propose transitions; certificates must check them.

## Acceptance

- The authority migration is complete; these proofs use its population rules
  and do not retain a second legacy counted-body synchronization mechanism.
- The helper transfer and protected-resource composition examples establish
  that runtime and ordinary resources follow the same contract rules.
- Fork/join, exact mutex counter, and one-shot publication verify through
  ordinary verify, profile, expand/reverify, and audit workflows. The parity
  demonstration and existing failure-path coverage remain green.
- Positive and hostile regressions cover wrong/stale authority, missing
  restoration, duplicate recovery, conservation, interference, lifetime end,
  synchronization failures, and forged certificates.
- Deterministic scaling tests cover increasing workers and synchronization
  operations, and fixed operations amid unrelated resources and history.
  Explicit proofs remain approximately linear up to indexing factors, without
  schedule enumeration or whole-history scans per step.
- The language inventory distinguishes implemented forms from proposals;
  diagnostics identify source obligations; each concurrent rule has a stated
  interpretation and runtime trust boundary. `scripts/check.sh` passes.
- Native execution claims satisfy the separate binding obligations above.

General atomic read-modify-write operations, reusable publication, fences,
condition variables, reader/writer locks, detached threads, lock-free
structures, concurrent reclamation, and C++ threading remain in
[broader concurrency support](concurrency-and-atomics.md). Deadlock freedom,
fairness, and termination need separate specifications and reasoning. They do
not follow from the safety model. Exclusive transfer of implicit stack/global/
static storage is also deferred. Delete this issue and its index entry when
its demonstrations, reviewed interfaces, tests, documentation, and binding
claims satisfy these acceptance criteria.
