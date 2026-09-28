# Exact-two counter: a bounded completion pool

Status: proposed surface interface, awaiting review; not implemented syntax.
The unchanged `mutex_counter.c` verifies for safety, but its exact-two result
is not yet proved. This proposal supersedes the earlier two-population design
in this file. It deliberately does not implement general shared `Count`.

## Why ordinary resources stop short

Ordinary quantities can express `owns n of increment_credit(p)`, package
credits inside a resource, and transfer credits through a mutex. They do not
establish a finite global supply. In the existing experiment, a worker needs
`n + 1 <= 2`; knowing `n <= 2` and owning an external credit does not imply it.
The authority could already contain two credits with another outside.
`mdtests/mutex_resource_quantity_requires_conservation.md` records this failure.

The parent also needs to establish the supply from its memory-only entry
contract. Assuming caller credits does not solve initialization. Existing
`constructs` can authorize ordinary abstract-token creation, so arbitrary
ordinary tokens cannot serve as authenticated receipts for increments.

The missing primitive is a conserved finite pool. Mutexes still provide only
access to its authority; the pool supplies the arithmetic conservation law.

## Proposed surface

Use three built-in resource types and three explicit proof operations. These
are language additions even though they require no new keywords or angle
parameters. Names below are proposed, not accepted Click syntax.

```text
abstract resource completion(p: struct mutex_counter*);

resource counter_state(p: struct mutex_counter*) {
    field value: uint32;
    guarded_by p->mutex;
    owns p->value;
    owns total: count_authority(completion(p));
    fact total.capacity == 2;
    fact value == total.completed;
    fact p->value == value;
}
```

`completion(p)` identifies the application protocol. It grants no ownership.
`count_authority(completion(p))` exclusively owns its capacity and completed
count; `count_credit(completion(p))` authorizes one completion;
`count_receipt(completion(p))` records one completion. Credits and receipts
support ordinary quantities. An ordinary `completion(p)` token is neither.

The authority exposes read-only model observations `capacity` and `completed`.
They are bounded nonnegative integers, with completed no greater than capacity.
The invariant's mixed integer/uint32 equality requires checked conversion,
not a wrapping arithmetic shortcut. Naming an authority or knowing its type
alone does not expose its current fields. Old observations remain snapshots.
This uses the existing named-resource field idiom, but implementing these
built-in fields and owned nested authority is part of the proposed extension.

The worker contract remains ordinary resource transfer:

```text
consumes count_credit(completion((struct mutex_counter*)argument));
produces count_receipt(completion((struct mutex_counter*)argument));
owns access: mutex_use(
    &((struct mutex_counter*)argument)->mutex,
    counter_state((struct mutex_counter*)argument)
);
```

Proposed operation shapes use ordinary named inputs and outputs:

```text
let { authority: total, credits: credits } = create_count(completion(p), 2);
let { authority: updated, receipt: receipt } = complete_count({
    authority: total, credit: credit
});
retire_count({ authority: total, credits: remaining, receipts: completed });
```

Creation returns capacity many credits and authority at completed zero.
Completion consumes one credit and the current authority, and returns the
updated authority and one receipt. Retirement consumes the authority and a
complete supply of credits/receipts. A zero quantity needs no resource token.
Output maps do not introduce implicit C parameters. Ordinary `fold`,
`unfold`, and `construct` do not mint these primitives or update their counts.
No additional user-defined resource algebra interface is needed for this slice.

## Conservation rule

For a fresh pool identity g, write A(g,N,n) for its exclusive authority,
P(g,p) for p pending credits, and D(g,d) for d completed receipts. Credits and
receipts compose additively within a generation. Authority validity requires:

```text
0 <= n <= N
0 <= p <= N - n
0 <= d <= n
```

These bounds concern all composed fragments, including fragments held by other
threads. Local ownership implies the corresponding lower bound; it never
implies that no fragments exist elsewhere.

The single update rule is:

```text
A(g,N,n) * P(g,1)  -->  A(g,N,n+1) * D(g,1)
```

It preserves every compatible frame. If other pending credits total p, then
p + 1 <= N - n before the update, hence p <= N - (n + 1) afterward. If other
receipts total d, then d <= n before, hence d + 1 <= n + 1 afterward.
Possession of the consumed credit proves n < N, so the update cannot exceed
the capacity. Capacity and addition are checked within the supported integer
range. The exact-two example uses N = 2.

Dropping a fragment cannot forge a receipt or invalidate these inequalities.
It can prevent the final exactness or retirement proof. No rule infers global
absence from an empty local resource context.

## Identity through modular contracts

Printed resource arguments are not a pool identity. Each `create_count` makes
a fresh generation, retained by authority, credits, and receipts. Reusing the
same address after retirement creates a different generation.

The proposed first slice elaborates a shared generation variable for matching
pool occurrences in a contract. In the worker above, the credit, output receipt,
and authority owned by the typed protected resource all refer to that variable.
This is an independently checked contract relationship, not a search heuristic.

- Entry verification assumes an arbitrary generation and arbitrary valid total.
  It must not start that total at zero.
- A caller instantiates that variable from actual resources and authenticates
  every occurrence against it. Printed type or address equality is insufficient.
- Folding records the owned authority's generation in the protected instance.
  Mutex publication and typed use shares retain that association. Lock freshens
  observations while preserving the association. Refolding and release must
  match that same generation; a replacement protected instance cannot switch
  the mutex to a different pool.
- A worker launch checks its credit against that exact typed use association.
  A join returns the receipt of that launched worker, exactly once.
- A function summary transports resources and relationships; it does not apply
  a sequential population count delta or install a child's snapshot.
- Multiple candidate generations for the same protocol in one contract are
  rejected in this slice. Supporting such contracts would require another design
  decision; do not silently unify distinct generations.

This deliberately limits the first implementation to an unconditional,
uniquely bound pool ingredient in a fixed-footprint protected resource. Both
independent contract verification and caller-side substitution need negative
regressions. Unique selection alone is not authentication.

## The unchanged counter proof

The parent creates A(g,2,0) and two credits after writing zero. It folds the
authority with the counter memory and publishes that ordinary resource through
mutex initialization. Each successful thread creation transfers one credit;
failed creation retains it. The C source remains unchanged.

A worker locks, unfolds the protected state, and obtains authority plus its
one credit. Their validity proves the completed count is below two. It executes
the existing C increment, completes one credit, then folds the updated state
and unlocks. The equality between the memory value and completed count checks
the connection between ghost accounting and the C operation. A missing
increment, duplicate increment, or duplicate completion fails this connection
or lacks a credit. Consuming a credit alone cannot satisfy the receipt output.

After joining every started worker and destroying the mutex, the parent
recovers the authority. The following bounds prove every cleanup state:

| Path | Returned/retained fragments | Completed count |
| --- | --- | --- |
| Mutex initialization fails | Two credits | Zero |
| First thread creation fails | Two credits | Zero |
| Second creation fails; first worker joined | One credit, one receipt | One |
| Both workers joined | Two receipts | Two |

For success, two receipts imply n >= 2 and capacity implies n <= 2. Thus
n = 2 and the invariant gives the required `counter->value == 2`.
Join order is irrelevant. The parent can retire each pool using the actual
fragments in the table.

Retirement requires p + d = N. Validity then forces p = N - n and d = n,
so no positive fragment can remain in a compatible frame. It also requires
that authority is actually owned and that normal loan recovery permits
consuming every supplied authority, credit, and receipt. Full supply does not
by itself discharge borrow obligations. It does
not scan unrelated resources. It does not reset a population by printed name.

## Scope and implementation acceptance

Implement this as generation-bearing resource primitives, separate from
sequential `(family, arguments)` population snapshots. Keep operations indexed
by their actual inputs; do not scan project-wide state or copy all histories.
The existing ordinary resource and mutex transfer paths should carry these
primitives with their checked associations.

Required checks:

- Fresh creation, zero capacity, bounded arithmetic, split/combine quantities,
  and the frame-preserving completion rule.
- No ordinary token constructor, resource fold, contract output, or join can
  manufacture a credit, receipt, authority, or second application of an update.
- Duplicate authority, mixed generations, stale receipts after reinitialization,
  missing/mismatched protected authority, replacement-pool publication,
  double completion, and early retirement
  are rejected with the missing resource or bound identified.
- A Count observation or old authority field cannot become a new observation of
  current state. Lock refreshes values without changing generation association.
- The unchanged C verifies its exact-two success result, both create failures,
  initialization failure, and reverse join order. Negative workers preserve the
  original incorrect C as their regression.
- Expansion produces a recheckable certificate; deterministic scaling tests cover
  independent pools and long explicit proof sequences; `scripts/check.sh` passes.

Do not add a general shared-population body, wildcard Count authority, resource
parameters, or a mutex-specific completion operation. A fractional authoritative
sum is another sound design direction, but introduces fragment shares and a
full-share equality rule. For this milestone the bounded pool fits the existing
quantity arithmetic and yields direct missing-credit/receipt diagnostics.

This document does not claim the exact-two C proof is complete. Implementation
is blocked on review of the proposed built-in resource and proof-operation
interface, including the implicit generation relationship described above.
