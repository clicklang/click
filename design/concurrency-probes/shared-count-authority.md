# Exact-two counter using ordinary counted resources

Status: superseded. Population authority replaced the counted-body model this
investigation explored: `authorized` families have bodyless members, a control
owns `authority(...)`, a mutex protects that control, and workers follow the
[worker authority protocol](../../docs/internals/worker-authority-protocol.md).
The counted-body mutex custody described below was deleted. The record is kept
for its reasoning.

A sequential control verifies exact value two with existing resource
declarations, `count`, `owns`/`consumes`/`produces`, `fold`, `open`, and `unfold`.
The unchanged pthread example is not yet verified for its exact result. The
bounded-completion-pool proposal stays shelved. Publication now restricts local
population body access as described below; concurrent exact-two accounting
remains open.

## Investigation: one mutex protects a counted population

Conclusion, 2026-09-28: this looks sound for the counter under the restricted
rules below. The existing population invariant supplies the conservation law;
the missing mechanism is exclusive access to its body under sharing. No need
for `sum_authority`, `sum_fragment`, `GhostId`, or a new algebra-definition
language has been established. This is a source-level investigation and a
semantic argument, not a checked concurrent proof or a formal soundness result.

### The proposed interpretation

A mutex associated with `remaining(p)` protects the body shared by all units
of that particular population. It does not take all membership units from
their owners or transfer those units to every acquirer. Different `p` values
can have different populations and locks. Pointer aliases must resolve to the
same checked population; pointer reuse must not revive an older association.

The intended worker clauses can use the existing forms:

```text
consumes remaining((struct mutex_counter*)argument);
owns access: mutex_use(
    &((struct mutex_counter*)argument)->mutex,
    remaining((struct mutex_counter*)argument)
);
```

This direct counted payload is a proposal: current mutex interfaces require a
folded exclusive instance, and named counted-payload transport is not supported.
Extending existing argument and binder forms to counted payloads is real work,
even if it needs no new grammar. An ordinary wrapper may also contain the
selected population, but it must carry the same checked body custody; owning
one nested unit must never create a second copy of that custody.

Initialization establishes the association from actual ownership and the
selected resource. The proposed rule does not depend on a mutex annotation.
Initialization now supports ordinary unannotated exclusive resources, with
declaration/schema and actual ownership checks; the declaration annotation is
retired. Both concrete and independently checked
typed-use paths accept the unannotated exclusive form. The frozen counter's
existing memory-safety sidecar uses it. Counted wrappers have the local custody
implementation below, but typed-use sharing of them remains refused.

### Implemented local access test

The local test now distinguishes membership from body permission:

- `mdtests/population_mutex_helper_held.md` initializes three units, deposits a
  wrapper containing one, and retains two. An ordinary helper whose contract
  says `owns member(p)` opens the population and reads its body under the lock.
- `mdtests/population_mutex_helper_unheld.md` calls the same helper without
  acquisition and fails with `Requires owns mutex_guard(&p->mutex)`.
- Companion negative fixtures reject a unit hidden in another wrapper at
  publication or release, a second mutex for the same population, and full
  population cleanup before mutex destruction.

The implemented payload is an ordinary field-bearing wrapper containing one
unconditional counted resource. Its `retained` field determines how many units
it contains (`owns retained of member(p)`). This uses existing syntax and a
meaningful quantity field; direct named counted payloads are still unsupported.
The previous local conservation fixture now uses this quantity instead of its
old dummy marker. Its C is unchanged and its contract supplies the complete
population for each initialization.

Publication checks that directly held units plus the wrapper's units equal the
current positive count. Acquiring returns the wrapper and restores body access
to the caller's retained units. Release requires the complete population again,
with no open body or memory loan, and makes retained units opaque. Destruction
recovers the local population representation. Count itself is unchanged by
these exchanges. Hidden units are refused rather than found by traversing
unrelated ownership. Custody uses an indexed population-to-mutex association;
resource updates visit only the selected population's occurrences.

This is a deliberately local slice. It cannot lend mutex-use authority for
this payload or transfer its units to workers. It does not implement fresh
counts across interference, worker effects, or join reconciliation. The checks
below remain the requirements for that next stage; passing this local pair is
not a concurrent exact-two proof.

### Publication and its ownership precondition

For the first slice, publish only an exact, positive, already initialized
population whose entire membership is owned locally. Require no active body
opening, body loan, pending worker, or existing custodian. The proof must
identify the participating owned quantities and establish that their sum
equals the current count. All-units ownership is checked, not assumed from the
fact that the population was recently initialized.

On successful mutex initialization, deposit one unit and the unique shared
body into the mutex. Keep the other units locally, with their body access now
subject to that mutex. Count does not change. Initialization failure preserves
the prior local access regime, units, and body. The deposited unit keeps the
existing positive-population invariant alive; it is not another resource type.

This transition can strengthen the access discipline without revoking anyone
else's permissions because there are no external units or body loans. It must
also remove local projections that would still grant access while unlocked.
A second mutex cannot publish the population: existing custody forbids it even
if all membership units later happen to be locally available during an
acquisition. Merely refolding or moving a unit never performs publication.

The implementation should validate explicit population quantities and tracked
wrapper contents, not discover ownership by scanning unrelated proof state.
The first slice can require directly available units at publication; arbitrary
nested-wrapper collection is not a prerequisite for the direct counter.

### Access, updates, and cleanup

Internally distinguish local body access, custody in an unlocked mutex, and
body access lent through one checked acquisition. This is permission metadata,
not a proposed surface resource or a second global population count.

| Operation | Required behavior |
| --- | --- |
| Move or wrap a unit | Preserve membership, count, identity, and custody. Supply no new body access. |
| Acquire | Return the deposited unit and exclusive body access with the guard; establish a current observation of the same population. |
| Open the population | Require an owned unit and valid local or acquired body access. Expose body memory and facts at the current count. |
| Create or consume units | Require body access and restore the invariant at the changed count. Initially support the existing fixed one-unit consumption only. |
| Release | Require a closed, restored body, one returned unit, and the matching acquisition; revoke body access and return custody to the mutex. |
| Join | Recover worker resources/use loans and reconcile its checked effect once. Do not physically consume units again. |
| Destroy | Require the existing lifetime conditions plus recovery of all population units for conversion back to the local access regime. Return the deposited unit and body access. |
| Final unfold | Use existing full-population cleanup after destruction. |

At destruction, count the mutex's deposited unit together with the recovered
caller units; the caller need not already own the escrowed unit directly.
Requiring all units at destruction is conservative but avoids returning a
sequential body-access regime while an external fragment still exists. Merely
recovering all mutex-use loans does not, by itself, prove every unit returned.
All count-producing paths must respect custody; blocking only consumption is
insufficient. The first implementation should reject shared production and
whole-population destruction inside an acquisition rather than guess rules.

### The ordinary-helper boundary is essential

Today, counted-resource entry setup and call preparation can materialize body
memory from a unit. Consequently, checking only the `open` tactic would leave
a bypass: an unlocked worker could pass its unit to an ordinary helper whose
independent proof assumes that body memory.

Recommended first-slice contract rule:

- A typed `mutex_use(mu, remaining(p))` input identifies that population as
  guarded in the independent contract. Its units provide no body memory or
  current Count facts until acquisition. Authentication happens at calls and
  create, not by trusting the written type alone.
- Existing unit-only sequential contracts retain their implicit body-access
  requirement. Calls must supply that access as well as the units. A caller
  with the guard and opened body can lend it to a synchronous helper while
  retaining the guard. An unlocked caller cannot.
- A helper receiving ordinary exposed memory can continue using its ordinary
  memory contract. It need not mention the mutex. Thread transfer remains
  refused for unit-only stateful contracts without a checked guarded protocol.

This is an explicit contract-elaboration rule, not a decision made from the
callee's implementation or from whichever permissions happen to be available
at a call. Its conservative limitation is that a unit-only forwarding helper
cannot accept guarded units outside the lock; the helper must carry the typed
use association too. General fragment-only contracts can be considered later
if this proves burdensome. Supporting every existing unit-only helper outside
the lock while retaining its old body assumptions would be unsound.

Failures can name `Requires mutex_guard(mu)` for missing acquisition and the
particular body fact for failed restoration. Publication/cleanup must show the
required quantity and count equality. A missing body loan inside a helper must
identify the guarded population and call requirement, not pretend its owned
unit is absent. The guard remains necessary but is not sufficient if its
payload/body has already been moved or lent elsewhere.

### Count observations and worker effects

Current Count is an observation, not a permanent fact about an independently
running worker. At acquisition take a fresh observation `N` constrained by
the body and actual units. In this counter, the deposited unit plus the worker
unit give `N >= 2`; the body gives `N <= 3` and `value == 3 - N`.
After the increment, consuming one unit establishes
`value == 3 - (N - 1)` before release. No worker entry count is substituted for
`N`. Earlier observations remain historical, with no new current-memory access.

Track a worker's own checked consumption independently of other workers'
changes. A function promising to consume one unit must discharge exactly that
effect. It cannot require its current global count to equal its entry count
minus one: other workers may run before its acquire or after its release.
Calls must transfer fulfillment evidence without fulfilling the caller's
obligation twice.

The parent can retain a projected final count from verified worker contracts,
as the existing abstract-population join protocol does. While workers remain,
that projection is not the count observable at an acquisition. Final join
establishes the completed cohort's exact net effect; it neither consumes again
nor overwrites a conflicting observation. Initially exclude parent count
mutations while a cohort is outstanding; parent guarded reads may observe a
fresh count. A later extension must include parent mutations in the same
conservation accounting.

For the frozen counter: initialize three units, deposit one, transfer one to
each successful worker. Each successful worker consumes one under the lock.
After every successful worker joins, the total is `3 - number_started`. The
parent recovers the retained unit at destruction, unfolds the remaining one,
two, or three units, and obtains value two, one, or zero respectively. A failed
create transfers and consumes nothing. The two join orders give the same
result. Partial join establishes no exact current value while the other
worker can still run.

### Source evidence and implementation obligations

The implementation was inspected at `205ba54e7`; the subsequent master change
`2b582ba4d` does not alter these paths.

| Existing path | What must change |
| --- | --- |
| `src/kernel/proof/execution.rs`, full-population cleanup | Reuse the ownership-equals-count premise for publication, while preserving units and transferring body custody instead of destroying the population representation. |
| `src/kernel/mutexes.rs`, `publish_declared` / `publish_with_interface` | Currently escrow one exclusive instance. Admit checked counted payloads and bind custody to the non-reused initialization identity. |
| `src/kernel/mutexes/assumed_protocol.rs`, `fresh_protected_payload` | Accepts unannotated leaf instances. Extend this to freshen a guarded population's observation without allocating a new population or new units. |
| `src/surface/proof/resources.rs`, entry/body materialization | Do not derive body memory and current facts from a guarded unit at entry. |
| `src/kernel/functions.rs`, body expansion and call transfer | Require body access at every authority-bearing projection and helper boundary. Static footprint calculation alone grants no ownership. |
| `src/kernel/proof/population_consumption.rs` | Retain invariant checking and effect fulfillment; add guarded body-access admission. |
| `src/kernel/functions.rs`, committed-consumption reconciliation | Replace the shared case's entry-total comparison with the function's own checked effect, retaining the sequential check where appropriate. |
| `src/kernel/threads.rs` and `src/kernel/spec.rs` | Distinguish a future cohort total from an acquired current observation; current code blocks Count whenever workers are pending. |
| `src/kernel/thread_confinement.rs` | Permit only authenticated guarded-population transfers; preserve the default stateful-population refusal. |

Internal population lifetime/custody identity must survive alias resolution,
wrappers, calls, workers, and new acquisition observations. Mutex initialization
already has a fresh identity; extend its checked association rather than
introducing a public ghost-name parameter for this milestone. Wildcard Count
must not bypass permissions on any matched population.

### First implementation and acceptance

The local wrapper slice now checks publication/failed initialization, guarded
body access, ordinary helper admission, release, destruction, and full cleanup
without threads. Direct named counted payloads remain a separate representation
extension; they are not required by this local wrapper test. Include both successful access and missing-lock helper
counterexamples before permitting worker transfer.

Then add arbitrary acquired counts, checked consumption effects across workers,
and join reconciliation. Preserve the original C and verify exact two, both
creation-failure cleanup paths, and reversed join order. Hostile cases must
reject a second mutex for the same population, incomplete publication, active
body loans, outside-lock helper access or production, stale Count assumptions,
wrong initialization identity, unfulfilled/double consumption, and premature
destruction. Every certificate path needs the same permission checks; expansion
and audit must agree. Use indexed custody/effect records and scaling regressions.

The rule removes the need to design another public algebra for this example,
but it is not a parser-only change. The principal implementation work is
closing all body-access paths and separating current observations from verified
future effects. Existing `count` and mutex machinery provide a plausible basis
for both. Implement this restricted rule before deciding whether a more general
resource-algebra interface is warranted.

## Accounting invariant

Use one ordinary population backed by the actual counter memory:

```click
resource remaining(counter: struct mutex_counter*) {
    owns counter->value;
    fact count(remaining(counter)) <= 3;
    fact counter->value == 3 - count(remaining(counter));
}
```

After the existing C writes zero, initialize three units from that memory.
One stays inside the protected resource; each worker gets one of the other
two units. The retained unit keeps the population body alive until cleanup.
It is accounting within the proof, not an extra C field or C operation.

The initial concurrent proposal wrapped a retained unit using existing syntax.
This shape remains unproved. The separate-body control below instead puts
memory directly in the protected state:

```click
resource counter_state(counter: struct mutex_counter*) {
    field marker: int32;
    owns remaining(counter);
    fact marker == 0;
}
```

The marker merely makes this an exclusive field-bearing resource under the
current representation. It carries no conservation information. This probe
also exposes a usability limitation: an exclusive wrapper with only an owned
child should not need a meaningless model field. Do not present that field as
part of the essential protocol or add one to the C source.

The worker's contract consumes an ordinary unit:

```text
consumes remaining((struct mutex_counter*)argument);
owns access: mutex_use(
    &((struct mutex_counter*)argument)->mutex,
    counter_state((struct mutex_counter*)argument)
);
```

Under the lock, the worker's unit plus the retained unit establish count at
least two. The shared body bounds count by three. Incrementing the C value
and consuming one unit preserve `value == 3 - count`. The last protected unit
prevents the body from disappearing during a worker's operation.

After every started worker has joined, conservation gives:

| Path | Remaining total | Counter value |
| --- | --- | --- |
| Mutex initialization fails | 3 | 0 |
| First thread creation fails | 3 | 0 |
| Second creation fails; first worker joined | 2 | 1 |
| Both workers joined | 1 | 2 |

The successful path then unfolds the last unit to recover counter memory.
Failure cleanup must recover the body from all remaining units. No receipt
family, count-credit family, count-authority family, or `create_count` operation
is part of this design.

## What actually verifies today

`mdtests/counted_resource_contribution_counter.md` is a passing sequential
control. Its seven verified functions:

1. Write zero and produce three `remaining` units by folding the memory body.
2. Preserve one unit and consume another while incrementing the uint32 value.
3. Call initialization and two contributions, unfold the final unit, and prove
   the returned value is exactly two.
4. Initialize directly after the C assignment with `fold(3 of remaining(p))`,
   call the two contributions, and again prove the returned value is two.
5. Initialize and recover all three units with `unfold(3 of remaining(p))`,
   proving the untouched value is zero.
6. Make one contribution, recover the two remaining units with
   `unfold(2 of remaining(p))`, and prove the value is one.
7. Recover a positive symbolic quantity `n` using `unfold(n of remaining(p))`
   when the contract supplies ownership and proves `count(remaining(p)) == n`.

The arithmetic proof explicitly establishes that subtracting one leaves at
least one unit and preserves the body equality. Existing population transitions
perform the count change at the function boundary. This is evidence that the
ordinary population invariant expresses conservation; it is not evidence that
the current mutex or worker transport supports the invariant.

A retained unit does not independently own the shared population body. Call
framing now leaves counted heads opaque, including inside ordinary wrappers,
so a callee's permitted mutation gets a fresh memory observation. Independently
owned sibling memory remains preserved. Regression coverage rejects identifying
the old counter value zero with its new value one across that call. Neutral
calls retain the population body's allocation lifetime independently of its byte
values. Typed definedness facts can follow checked pointer aliases, including
field offsets, only with matching types and valid memory continuity.

The original `mutex_counter.c` was left unchanged in both probes below. No
helper calls were inserted into its C to imitate the sequential control.

## Observed blockers in the unchanged C

### Initialization inside the parent

After the parent's two local declarations and `counter->value = 0u`, the probe
uses existing syntax:

```text
fold(3 of remaining(counter));
```

This local initialization now verifies. `CheckedResourceRewrite` delegates the
allocation to `src/kernel/proof/population_initialization.rs`; ordinary
representation rewrites still require definitionally equal population states.
The new rule checks a single fresh population, consumes its independently owned
memory body, proves the invariant from input facts at the proposed count, and
preserves the remaining execution state. Active borrows, existing populations
(including zero-count entries), and existing resource heads prevent allocation.
It does not interpret an absent population as an arbitrary entry count of zero.

The first supported slice is an unconditional, nonrecursive memory body with
one pointer argument and nonempty fixed-size ranges. Unsupported alias contexts
are refused conservatively. Initialization does not yet give a population
cross-thread identity or synchronized body access. Persistent population and
resource-head indices keep checks local to the changed population; deterministic
scaling regressions cover unrelated populations, heads, and path facts.

### Population body beneath a mutex wrapper

The worker probe reaches its lock and fails:

```text
protected mutex resource has no checked memory footprint
```

Its wrapper owns one `remaining` unit, whose population body owns the counter
memory. The current mutex path cannot derive and transfer that protected body.
`src/kernel/mutexes/assumed_protocol.rs` builds fresh protected observations
under restricted payload rules, and `src/kernel/thread_confinement.rs` keeps
stateful populations thread confined until synchronization owns their body.

This requires general composition support: the mutex owns the unique shared
body/access authority while population units can cross threads under that
protocol. Merely holding a unit must not expose memory or current Count facts
outside the lock. Do not remove thread confinement globally or freshly invent
the population when acquiring a wrapper.

## Scope-close consumption

The accounting gap is reproducible without pthreads. For a function that
increments the value and then returns it, the following shape now verifies
with the arithmetic facts supplied in the regression:

```text
// Function contract: owns remaining(p); consumes remaining(p);
open(remaining(p)) {
    step(); // the existing C increment
}
open(remaining(p)) {
    step(); // the existing C return reads the protected value
}
```

Before this change, closure required `p->value == 3 - count(remaining(p))`, but the
increment established `p->value == 3 - (entry_count - 1)` and current Count
still denoted `entry_count`. The sequential control succeeds because its
`execute()` reaches the return inside the open scope. Unlock must happen before
return, so return-time accounting cannot establish the mutex invariant.

The approved rule uses existing syntax. First try to close `open` by restoring
the invariant with unchanged membership and Count. If that cannot be proved,
closure may fulfill an outstanding `consumes` effect of the enclosing function
for this population. No new consumption statement, resource type, or keyword is
introduced. The single-unit case is implemented and covered by
`mdtests/population_consumption_at_close.md`. After a consuming close, another
ordinary `open` can expose the surviving body for a subsequent C read.

The invariant is still required at closure. Consumption changes the Count at
which it must hold; it does not excuse a missing invariant. In the example,
let the current total be `N`. After the C increment, consuming one owned unit
changes the total to `N - 1`, and closure must prove
`p->value == 3 - (N - 1)`. The ordinary close instead requires
`p->value == 3 - N`. Merely placing `open` last in a block grants no exemption.

The checked transition must establish all of the following:

- The enclosing contract has an unfulfilled consumption for this exact
  population. Evaluate entry arguments at function entry, even if C later
  reassigns its parameters. A contract effect is an obligation, not ownership.
- The proof owns the units being consumed and has valid access to the open
  shared body. A view or a declaration alone cannot authorize the transition.
- Subtracting the consumed quantity leaves a positive total and restores every
  body fact at that total. The worker's retained unit keeps this body alive.
  Final-population cleanup remains a separate operation.
- The transition spends those units, closes body access, and preserves all
  unrelated resources, populations, memory, and active-loan restrictions.
- A checked record marks this part of the contract effect as fulfilled on this
  execution path. A later scope cannot fulfill it again, and return must
  reconcile it with the remaining effect rather than spend it a second time.
  Calls must keep caller and callee obligations distinct.

The implementation admits one unconditional single-unit consumption clause for
the resource family and rejects production of that family in the same
contract. It does not search for an amount that makes the invariant true.
Consumption inside a loop, general partial fulfillment of symbolic effects,
and competing candidate effects remain unsupported. A later extension needs
checked loop/partial-effect accounting; it must not reset a spent effect.

The kernel records the committed unit in persistent function-local state.
Callee binding starts a separate record, and returning preserves the caller's
record. The combined execution event is tied to the enclosing contract and
checks ordinary restoration after the consumption. Reopening interprets body
facts at the current Count. Return reconciles the tracked total with the
entry-based contract effect rather than silently resetting a differing total.
Kernel regressions cover actual ownership, entry argument reassignment, repeated
consumption, unchanged unrelated state, active memory loans, false invariants,
and keeping the last unit alive. Sidecars cover ordinary closure before a
consuming close, reopening, branches, nested reads, exact two calls, and
rejection of missing contracts, incorrect increments, and repeated or nested
extra consumption.

Report failed obligations with Click expressions, such as
`Requires remaining(p)` or `Requires p->value == 3 - count(remaining(p))`,
and identify whether Count is before or after the proposed consumption when
that matters. Missing contract authorization should name the required
`consumes remaining(p)` clause. Do not expose internal bookkeeping terminology
as the explanation of the user's proof failure.

Acceptance starts with the early-close sequential regression, then composes it
with unlock. Negative tests must reject absent consumption clauses, viewed or
missing units, missing increments, repeated fulfillment, consuming the last
unit, and changes to unrelated populations. A successful ordinary close must
leave the contract effect outstanding. A successful consuming close followed
by return must account for exactly one unit. Branches and nested calls must
preserve that accounting, and expansion must produce a checkable certificate.

A separate classification limitation rejects a guarded exclusive wrapper whose
model fact mentions `count(remaining(p))`: it currently treats any Count mention
as observing the wrapper's own population. Supporting foreign-population facts
must preserve the same authenticated population across acquisitions and must
not manufacture its total from the locally visible units.

## Conservation through a locally owned mutex

`mdtests/population_conservation_local_mutex.md` isolates the conservation rule
from cross-thread transfer. A sequential helper receives a protected wrapper
containing one `remaining(p)` unit and consumes a second unit. It initializes
a local mutex, acquires it, unfolds the wrapper, and opens the population body.
After the C increment, scope closure commits the consumption and proves
`p->value == 3 - count(remaining(p))` at the decreased count. The helper folds
the wrapper, unlocks, destroys the mutex, and returns the retained unit inside
the wrapper. Its caller initializes three units, invokes the helper twice,
recovers the last unit's memory, and proves the returned value is two.

This is a synthetic sequential control under the modeled pthread assumptions,
not a replacement for the unchanged concurrent C. Its mutex is local to each
helper call, and its contract can require a current Count bound because no
other worker is running. The negative control increments by two while consuming
one unit and fails with
`Requires p->value == (3 - count(remaining(p))) after consumption`.

The final cleanup also tests that proof-only cell materialization preserves
unrelated memory views. Population cleanup exchanges only the selected units
and body; it must not normalize or discard framed mutex-storage observations.

The remaining concurrency rule is body custody, not another arithmetic law:
publication must bind this population to the mutex lifetime; worker units must
remain opaque outside an acquisition; acquisition must establish a fresh
observation of the same population; consuming closure must spend the worker's
unit while restoring the shared body; and final join must connect the verified
net effects to the total used at destruction. Neither a fresh population per
acquisition nor a Count copied from worker entry is valid under interference.

## Join accounting prerequisite

A reduced abstract-ticket example exposed a stale total: after joining a worker
that consumed the only ticket, the parent could still prove Count was one.
Worker completion returned resources but did not update the population total.

The checked join rule retains each observed population's baseline and reserves
its eventual total. Successful create adds its verified resource effect to that
reserved total; failed create adds nothing. Current Count remains unavailable
until every outstanding worker for the population has joined. Each join returns
only that worker's resources and spends its completion right once. The final
join publishes the accumulated total, preserving unrelated population changes.
Independent populations can complete in either order.

Multiple workers may consume fixed quantities from the same ordinary abstract
population, or return their units unchanged. Both the new worker and all existing
workers must have fixed non-increasing effects and state-independent pure
contracts. A worker whose contract observes current Count remains exclusive:
its entry/exit assumptions cannot silently survive interference. Production,
symbolic effects, and synchronous transfers while workers are outstanding are
conservatively excluded from overlap. Neutral workers still reserve Count;
matching entry and exit quantities do not promise unchanged intermediate totals.

The shared-abstract-population regressions cover both join orders, both creation
failure paths, neutral effects, and rejection of observations after a partial
join. They are separate from the unchanged mutex counter. This accounting
supports overlapping abstract units; stateful populations still need authenticated
body custody under the mutex before they can cross worker boundaries.

## Protected-body control using separate ordinary resources

The Iris-style control in `mdtests/mutex_population_separate_body.md` separates
physical ownership from contribution accounting. Its `counter_state` owns
`counter->value` directly, with the existing model field recording its current
value. The worker also receives one abstract `contribution(counter)` unit.
Lock returns the protected state and guard; unfold supplies memory ownership;
fold and unlock return it. The unit itself has no memory body.

This control uses the unchanged `mutex_counter.c` and verifies both workers,
both create-failure paths, and join accounting: the remaining total is two
before either worker starts, one after the sole successful worker joins, and
zero after both join. The parent receives the initial units as contract inputs.
Unused units on failure are consumed at the parent's return, after the explicit
intermediate total checks. This is not local population initialization.

`mutex_population_body_helper.md` checks that protected memory can be passed to
an ordinary helper after acquisition. The helper needs its ordinary memory
contract, without a mutex parameter or guard clause. Synchronous call summaries
frame the caller's protocol ledgers; ordinary mutable effects still cannot
write reserved mutex storage. Negative direct-read and helper-call controls
show that a contribution unit plus `mutex_use` supplies no protected memory.

This establishes body access through the existing protected-resource transfer.
It introduces no additional body-permission resource and does not change the
sequential memory-backed population rules above. In particular, it does not
make a memory-backed population unit safe to send to a worker.

The missing part is the conservation relation between the protected value and
the external units. `mutex_population_missing_value_relation.md` retains the
same source and accounting proof, but rejects an exact-two postcondition.
The present contracts allow arbitrary protected value changes, so consuming
two units alone cannot establish two increments. The next rule must let the
protected state maintain the accounting relation and require the corresponding
unit transition when restoring it. Simply allowing a mutable `count(...)`
fact in an exclusive resource is insufficient: a separate helper must not
consume a unit and invalidate that folded resource's fact. This dependency
must be checked before broadening the existing declaration restriction.

The earlier wrapper containing only one `remaining` unit is an investigation,
not a demonstrated concurrent representation. Do not infer ownership of the
shared body merely because such a unit occurs inside an exclusive wrapper.

## Subsequent obligations, not yet demonstrated by the probes

- **Compose consumption with unlock.** Early consumption now composes with a locally
  owned mutex in the sequential control above. The worker must use the same
  checked transition under shared body custody; that concurrent composition
  remains unproved.
- **Authenticate population identity.** Publication, typed mutex use, external
  worker units, and replacement protected states must refer to the same
  population. A fresh acquisition changes observations, not that identity.
  Address/type equality alone must not join unrelated lifetimes.
- **Recover exact totals only when justified.** Joining the first worker cannot
  imply the current count is two while the second may already have consumed its
  unit. Retain verified net effects through the participation protocol and expose
  exact totals when the relevant workers/rights have returned. Never copy a
  child's saved count into the parent or infer total count from local holdings.
- **Keep observations scoped.** For mutex-shared populations, current Count observations
  require valid body access; prior observations remain historical facts. An independently verified
  worker begins with an arbitrary valid total, never a chosen entry zero.

## Implementation order and acceptance

Checked local initialization and full-population cleanup are implemented for
this control. Cleanup uses ordinary quantity syntax, `unfold(n of remaining(p))`.
It requires the requested quantity to equal the total and consumes all those
owned units, including separately held pieces, to recover one shared body.
The kernel rejects partial or zero ownership, an open body, and active loans.
Unfolding is a representation change: the existing contract transition still
owns logical consumption; cleanup does not silently reset the ledger.

The next proposed step is the restricted population publication rule described
at the top of this document, followed by guarded count transitions and worker
accounting. The original pthread C stays the end-to-end regression throughout.

Each step needs negative coverage for forged/duplicated units, unrelated
population changes, stale observations, mismatched lifetimes, missing or double
increments, and count effects applied twice. Both create-failure paths and
reverse join order must work. Expansion must yield checkable certificates and
`scripts/check.sh` must pass. Representation changes must meet the existing
indexed, delta-proportional verification requirements.

The sequential evidence establishes the existing population rules, but does
not establish concurrent custody. The investigation above specifies the missing
ownership transfer without assuming a need for another surface resource type.
