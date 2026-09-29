# Exact-two counter using ordinary counted resources

Status: implemented sequential controls and historical concurrency
investigation. The next-step recommendation is now
[explicit fractional authority](explicit-authority.md), a design proposal for
review. It replaces the shared-body-custody direction below; those shared
rules were not implemented. Existing counted-resource semantics are unchanged.

A sequential control verifies exact
value two with existing resource declarations, `count`, `owns`/`consumes`/
`produces`, `fold`, `open`, and `unfold`. The unchanged pthread example is not
yet verified for its exact result. The earlier attempt to avoid all additional
resource interfaces did not resolve concurrent body authority. The new proposal
explicitly reviews that choice. The bounded-completion-pool proposal stays shelved.

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
    guarded_by counter->mutex;
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

The original next step was to compose population-body access with mutexes,
commit guarded count transitions, and connect worker accounting. That direction
is paused in favor of the [explicit-authority proposal](explicit-authority.md):
keep memory in the protected resource, put a separate authority beside it, and
return contribution shares through ordinary join transfers. The original
pthread C stays the end-to-end regression throughout.

Each step needs negative coverage for forged/duplicated units, unrelated
population changes, stale observations, mismatched lifetimes, missing or double
increments, and count effects applied twice. Both create-failure paths and
reverse join order must work. Expansion must yield checkable certificates and
`scripts/check.sh` must pass. Representation changes must meet the existing
indexed, delta-proportional verification requirements.

The sequential evidence establishes the existing population rules, but does
not establish concurrent custody. The replacement design exposes the missing
authority and update operations explicitly; its proposed surface additions
require review before implementation.
