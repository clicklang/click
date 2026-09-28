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

This issue is the current implementation roadmap. The older
[contract and diagnostics record](../docs/internals/concurrency-contracts-and-diagnostics.md),
[mutex contract design](../docs/internals/mutex-resource-contracts.md), and
[resource-argument record](../docs/internals/resource-parameters.md) retain
historical checkpoints and proposals. Their chronological status statements
must not override the current state below. Consolidating those records is the
first cleanup step, not a reason to implement every earlier proposal.

## Current state

| Demonstration | Verified today | Still missing |
| --- | --- | --- |
| [Disjoint fork/join](../examples/concurrency-fork-join/fork_join.click) | Exact outputs, ownership transfer, stable input loans, matching joins, and create-failure cleanup | Native runtime validation and broader threading APIs |
| [Even/odd locking](../design/concurrency-probes/mutex_held_parity.click) | Conditional acquisition across loop iterations, final unlock, and destruction | The conditional acquisition abstraction with protected payloads or use-loan-backed guards |
| [Shared-worker counter](../design/concurrency-probes/mutex_counter.click) | Worker and parent safety, shared typed use permissions, create-failure cleanup, and final destruction | The exact final value of two |
| One-shot publication | Design obligation only | Checked release/acquire semantics and a frozen C demonstration |

The parity loop works both through an ordinary conditional guard resource and
[direct conditional ownership in its loop contract](../design/concurrency-probes/mutex_held_parity_direct.click).
`loop_guard` is an example resource name, not a built-in construct.

The counter's typed use permissions identify the protected resource. Successful
creation transfers a checked worker share while retaining a parent share;
failure leaves authority unchanged. Joins recover shares into the current
ledger in either order. Destruction requires complete recovery. Shared
acquisition and release forget observations consistently with interference;
completed workers alone do not establish the final counter value.

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
| `guarded_by p->mutex;` | Declaration-level association with a pthread mutex field | Supported today; review whether initialization's checked association can replace or generalize it |
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
restriction. The shelved `count_authority` and `create_count` proposal is not
an accepted language extension.

The current `guarded_by` parser requires a struct pointer's pthread mutex
field with the modeled layout. That excludes a direct standalone mutex-pointer
annotation. Any redesign must retain authenticated initialization associations,
resource ownership checks, and stale-initialization rejection; merely deleting
the check is not sufficient.

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

Exact concurrent results need a relation between contributions held by workers
and the state protected by the invariant. Iris's
[counter construction](https://plv.mpi-sws.org/coqdoc/iris/iris.heap_lang.lib.counter.html)
uses ghost resources for such a relationship. This motivates checked
conservation; it does not choose a Click surface interface.

## Ordered implementation plan

### 1. Remove abandoned machinery and consolidate status

The unused resource-description parameter substitution and opaque parameter
scaffolding have been removed. `<P: Resource>` was never accepted by the
parser. `ResourceDescription` remains for current mutex associations.
Status consolidation in the linked design records remains.

Retain the implemented, tested named resource-reference arguments. A parameter
such as `target: cell(p)` denotes an occurrence, not a resource-type template.
Its ordinary ownership and reference checks are useful independently of locks.

Record the separate limitation that nested resource-type syntax currently has
special parser handling for `mutex_use`; user-defined resource constructors do
not have general resource-type parameters. Do not activate the abandoned
templating implementation merely to remove this special case.

Replace contradictory historical status statements in the linked design
records with one supported-feature inventory and clearly marked proposals.
Keep disabled runtime binder entries identified as unfinished work.

### 2. Make acquiring and releasing helpers ordinary contracts

Implemented for the direct named subset above; pause here for contract and
implementation review before starting step 3. A verified C helper can lock and
return a fresh guard and protected state, and a releasing helper consumes those
resources and unlocks. The [contract record](../docs/internals/mutex-resource-contracts.md#acquiring-and-releasing-helpers)
and executable example show the existing syntax and current boundaries.

The body must establish the actual protocol effect; a declared output cannot
invent a guard and a consumed guard cannot simply be discarded. Caller
summaries retain initialization and lifetime dependencies and forget protected
observations affected by the helper. The acceptance requirements remain:
reject duplicate or stale acquisitions, replacement of a promised preserved
guard, release without restored state, and destruction while a guard or use
loan survives. These transfers do not authorize moving pthread guards between
threads. Direct `pthread_mutex_t *` sidecar parameter spelling is a separate
existing parser limitation, retained as a frozen negative regression.

### 3. Complete the mutex-protected counter

Prove that the unchanged [counter C](../design/concurrency-probes/mutex_counter.c)
finishes at exactly two when both workers are created and joined successfully.
Preserve safety and cleanup for both create-failure paths and either join order.

The [ordinary-resource control](../design/concurrency-probes/shared-count-authority.md)
now proves exact two sequentially using a memory-backed `remaining(p)`
population and `p->value == 3 - count(remaining(p))`. Checked local
initialization creates three units from the owned memory body. Each contribution
consumes one; the retained unit keeps the body alive. Full-population cleanup
recovers the body from a positive exact total, including a symbolic quantity.
These implemented rules do not yet establish the concurrent result.

The [scope-close consumption rule](../design/concurrency-probes/shared-count-authority.md#scope-close-consumption)
is implemented for a single unconditional unit effect. Next compose shared-body
custody with the mutex and carry checked worker effects through joins. `open` closure first attempts ordinary restoration;
otherwise it may fulfill an outstanding `consumes` effect, spending owned units
and proving the invariant at the decreased Count. The same effect must not be
applied again at another scope or at return. The checked rule uses existing syntax.
Symbolic partial effects, competing effects, and consumption inside loops
remain outside the implemented slice.

Mutex acquisition must preserve population identity and authorize current
observations. Joining one worker must not publish an exact current total while
another worker may have changed it. Existing sequential `count(...)` alone
does not provide this authority. Keep the separate authority-resource proposal
shelved; any further surface interface requires review before implementation.

Reject missing or doubled contributions, incorrect increments, fabricated
credits, mismatched populations, and reuse of old counter observations. Preserve
the [current missing-conservation regression](../mdtests/mutex_resource_quantity_requires_conservation.md)
until a stronger contract actually supplies the missing relationship.

### 4. Test protected-resource composition

First verify a mutex protecting an ordinary resource with a named child. Then
verify a small example whose protected ownership footprint changes, such as
an allocated collection that grows while locked. Freeze each C example before
adapting the verifier; do not flatten the source or resource structure just to
fit the current leaf restriction.

Use these examples to decide what support for nested resources, recursive
assertions, changing footprints, and payload-bearing conditional loop guards
is required. They should extend ordinary resource reasoning, not create a
parallel mutex-specific assertion language.

### 5. Review the language against what the proofs use

Compare the implemented interfaces, the intended design, and the contracts
actually used by the helper, counter, and composition examples. Decide whether
`guarded_by` adds necessary information beyond initialization, and whether a
user-defined resource genuinely needs resource-type parameters. Do not add a
general parameter language in anticipation of possible future examples.

This review precedes further expansion of concurrency vocabulary. One-shot
publication remains the next independent launch milestone below.

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
