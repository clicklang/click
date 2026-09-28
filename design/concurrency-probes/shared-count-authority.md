# Exact-two counter using ordinary counted resources

Status: existing-resource investigation. A sequential control verifies exact
value two with existing resource declarations, `count`, `owns`/`consumes`/
`produces`, `fold`, `open`, and `unfold`. The unchanged pthread example is not
yet verified for its exact result. No new built-in resource type is justified
by this investigation. The earlier bounded-completion-pool proposal is shelved.

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

The intended wrapper uses existing declaration syntax:

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
control. Its four verified functions:

1. Write zero and produce three `remaining` units by folding the memory body.
2. Preserve one unit and consume another while incrementing the uint32 value.
3. Call initialization and two contributions, unfold the final unit, and prove
   the returned value is exactly two.
4. Initialize directly after the C assignment with `fold(3 of remaining(p))`,
   call the two contributions, and again prove the returned value is two.

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

## Subsequent obligations, not yet demonstrated by the probes

- **Commit consumption before unlock.** The worker must restore the invariant
  at the decreased population while still holding the lock. Existing return-time
  consumption cannot leave the body invalid between unlock and return. Closing
  `open` needs a checked transition that return certification recognizes exactly
  once. Whether existing scope syntax suffices needs an implementation probe.
- **Authenticate population identity.** Publication, typed mutex use, external
  worker units, and replacement protected states must refer to the same
  population. A fresh acquisition changes observations, not that identity.
  Address/type equality alone must not join unrelated lifetimes.
- **Recover exact totals only when justified.** Joining the first worker cannot
  imply the current count is two while the second may already have consumed its
  unit. Retain verified net effects through the participation protocol and expose
  exact totals when the relevant workers/rights have returned. Never copy a
  child's saved count into the parent or infer total count from local holdings.
- **Finalize an entire owned population.** Failure paths own two or three units.
  Generalize finalization from the existing single-last-unit case to a requested
  quantity proved equal to the total, while checking all borrow obligations.
- **Keep observations scoped.** For mutex-shared populations, current Count observations
  require valid body access; prior observations remain historical facts. An independently verified
  worker begins with an arbitrary valid total, never a chosen entry zero.

## Implementation order and acceptance

Checked local initialization is implemented for the memory-backed slice above.
Next implement full-population finalization independently of concurrency, then
compose population-body access
with mutexes, commit guarded count transitions, and connect worker accounting.
The original pthread C stays the end-to-end regression throughout.

Each step needs negative coverage for forged/duplicated units, unrelated
population changes, stale observations, mismatched lifetimes, missing or double
increments, and count effects applied twice. Both create-failure paths and
reverse join order must work. Expansion must yield checkable certificates and
`scripts/check.sh` must pass. Representation changes must meet the existing
indexed, delta-proportional verification requirements.

The evidence currently supports extending ordinary resource semantics rather
than adding specialized completion primitives. It does not yet establish that
every needed operation is expressible without any further surface decision.
If a genuine syntax gap remains, identify its exact missing rule first.
