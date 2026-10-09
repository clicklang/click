# Explicit authority for the shared counter

Status: superseded. The exclusive `authority(...)` resource it proposed was
adopted, without fractional authority; see
[object-anchored population authority](../../docs/internals/authority-establishment-review.md).
The text below is the original 2026-09-28 proposal.
The [counted-population investigation](shared-count-authority.md#investigation-one-mutex-protects-a-counted-population)
now recommends checking whole-population publication under an ordinary mutex
before adding this interface. The earlier recommendation below was premature:
the existing Count invariant already supplies a conservation relationship.
Nothing in this document is a verified Click example or an implemented new
interface. The frozen input remains
[`mutex_counter.c`](mutex_counter.c).

## Alternative considered

Use a fractional authoritative sum: one exclusive authority records the total,
and workers hold shares recording their individual contributions. The mutex
protects the authority and the C cell together. Joining returns a worker's
share with its updated contribution. Combining every share establishes the
exact total when compared with the authority.

This is a closer correspondence to Iris than inferring population-body
authority from a retained membership unit. Iris already has a contributed
counter built with `frac_authR natR`: shares split, an increment increases both
the authoritative value and a contribution, and a full share supports an exact
read. Its implementation uses CAS; we propose the same accounting structure
inside Click's existing mutex transfer. See the
[Iris contributed counter](https://plv.mpi-sws.org/coqdoc/iris/iris.heap_lang.lib.counter.html),
particularly `ccounter_op`, `incr_contrib_spec`, and `read_contrib_spec_1`.

Prefer this to introducing separate pending and completed token families. A
share with contribution zero is useful before work, and the same share with
contribution one is the completion evidence afterward. The share is conserved;
the contribution changes. There is no extra retained third unit.

Implement one checked algebra instance first. Expose its ownership and updates
in contracts; defer arbitrary user-defined algebra declarations. This does add
proof capabilities. It does not disguise them as ordinary empty resource
definitions that the current kernel could already justify.

## The mathematical interface

Use the following notation in this section only:

| Assertion | Meaning |
| --- | --- |
| `A(g, N)` | Exclusive authoritative total `N` for fresh ghost identity `g`. |
| `F(g, q, n)` | A positive share `q` with recorded contribution `n`. |
| `P(p, g)` | The ordinary protected resource: counter memory plus authority for `g`. |

Totals and contributions are nonnegative mathematical integers. Shares are
positive rationals at most one. They measure participation in this accounting
object, not fractions of C memory permission. Even a full `F` supplies no
memory ownership and no authority to update the total alone.

For each identity, fragment shares compose by addition, as do their
contributions. A combined share cannot exceed one. In the presence of
`A(g, N)`, the combined contribution is at most `N`; when the combined share
is exactly one, it equals `N`. Two full authorities for the same identity are
invalid. Positive shares cannot be duplicated, even when their contribution
is zero.

These are the relevant properties of
[Iris fractional authority](https://plv.mpi-sws.org/coqdoc/iris/iris.algebra.lib.frac_auth.html):
`frac_auth_frag_op`, `frac_auth_agree`, `frac_auth_included_total`, and
`frac_auth_update`. Click initially exposes only exclusive authority, not
Iris's additional fractional-authority modes.

The checked operations are:

| Operation | Requires | Produces or establishes |
| --- | --- | --- |
| Allocate | `N >= 0` | Fresh `g`, `A(g, N)`, `F(g, 1, N)`. |
| Split | `F(g, q, n)`, positive `q1,q2`, `q1+q2=q`, nonnegative `n1,n2`, `n1+n2=n` | `F(g,q1,n1)` and `F(g,q2,n2)`. |
| Combine | Two owned fragments for the same `g`; combined share at most one | Their summed share and contribution. |
| Add | `A(g,N)`, `F(g,q,n)`, `d >= 0` | `A(g,N+d)`, `F(g,q,n+d)`; same identity and share. |
| Agree | `A(g,N)` and `F(g,1,n)` | Fact `N == n`; both resources preserved. |
| Retire | `A(g,N)` and `F(g,1,N)` | Consume both; no memory effect and no subsequent reuse of `g`. |

For Add, any external fragments retain the same share and contribution. If
their combined contribution is `k`, `n+k <= N` implies
`n+d+k <= N+d`, and equality at full combined share is preserved. The rule
does not need to find or inspect those fragments. This is a local arithmetic
justification of our proposed specialization, corresponding to Iris's
[natural-number local update](https://plv.mpi-sws.org/coqdoc/iris/iris.algebra.numbers.html)
and its lifting through fractional authority.

Retire is a deliberately narrower cleanup policy than arbitrary forgetting.
Full share rules out another positive fragment in the frame; exclusive
authority rules out another authority. Forgetting a fragment, if otherwise
permitted, does not decrement `N` or manufacture completion evidence. It makes
full-share agreement and this cleanup unavailable.

Allocation must use a fresh logical identity, as in
[Iris ghost ownership allocation](https://plv.mpi-sws.org/coqdoc/iris/iris.base_logic.lib.own.html).
Two allocations at the same C address remain different accounts. A ghost name
is freely copyable identification; it confers no ownership. Moving a fragment
into a wrapper or another thread changes neither total nor contribution.

## The proposed surface, explicitly separated from existing syntax

The names below are candidates, not reserved words or implemented library
declarations:

| Proposed interface | Observations |
| --- | --- |
| `sum_authority()` | `group: GhostId`, `total: Integer`. |
| `sum_fragment()` | `group: GhostId`, `capacity: Integer`, `weight: Integer`, `amount: Integer`. |

`GhostId` would be a new opaque proof-only value type. It supports identity
comparison and use in resource arguments and model fields, but no numeric or
pointer casts. `Integer` already exists. Allocation chooses an immutable
positive capacity `K`; a fragment's share is `weight / K`. All fragments of
one group have that capacity, and `0 < weight <= K`. Thus the first interface
can use integer weights instead of introducing a rational type or interpreting
ordinary `1 / 2` as a fraction. Capacity two gives the two workers weight one
each. This is a fixed-denominator restriction of the algebra, not a claim that
Iris fractions have integral weights or a fixed capacity.

The identity needs to survive splitting, refolding, and replacement payload
instances. A resource occurrence reference names one occurrence; the C pointer
can be reused. Neither alone is the shared account identity required here.
Expose that distinction through `GhostId` rather than a new resource-description
parameter. Its kernel representation may reuse existing fresh-name machinery.

These resources are opaque: ordinary `fold`, `construct`, field assignment,
or a user-written `produces` declaration cannot mint them or change their
observations. Only checked allocation, split, combine, and update operations
can do so. A user helper must prove its transfer using those operations.
Resource types alone grant nothing. `views` cannot authorize an update, split,
retirement, or memory access.

The protected resource would have this shape (proposal, not parser-ready
evidence):

```text
resource counter_state(p: struct mutex_counter*, group: GhostId) {
    field total: Integer;
    owns p->value;
    owns ledger: sum_authority();
    fact ledger.group == group;
    fact ledger.total == total;
    fact total >= 0;
    fact to_integer(p->value) == total % 4294967296;
}
```

The modulo relation is intentional: the unchanged C uses unsigned 32-bit
addition. An independently checked worker cannot assume that other
contributions leave the mathematical total below the machine limit. Its
contract can allow arbitrary nonnegative totals and still prove this relation
after unsigned wraparound. At final total two it gives the ordinary exact
value two. The cross-domain arithmetic bridge needs a checked proof; this
document does not assert that the current tactics already provide it.

For `p = (struct mutex_counter*)argument`, the worker's proposed clauses are:

```text
owns part: sum_fragment();
owns access: mutex_use(&p->mutex, counter_state(p, part.group));
ensures part.group == old(part.group);
ensures part.capacity == old(part.capacity);
ensures part.weight == old(part.weight);
ensures part.amount == old(part.amount) + 1;
ensures result == 0;
```

`p` here abbreviates the cast, not an added C or contract parameter. The
owned fragment introduces its identity through an ordinary resource binder;
no free `g`, implicit type parameter, or new function-header parameter syntax
is hidden in this sketch. Dependent arguments such as `part.group` must be
checked from the owned input and retained as stable identity through calls.
Group/capacity/weight guarantees are written out to make the transfer plain;
whether immutable observations later make them redundant is a usability
decision, not permission to omit their kernel checks.

Existing `owns`, `consumes`, and `produces` still describe resource transfers.
This worker preserves and updates a named instance, so `owns` fits better than
consuming a unit. A split consumes one fragment and produces two; a combine
does the reverse. The protected wrapper is an ordinary user resource whose
child happens to have a checked algebraic implementation.

The parent's public contract retains ordinary memory ownership, requires the
existing mutex-storage alignment, and guarantees `result == 0 or result == 1`.
Its new result clauses would be:

```text
ensures result == 1 implies counter->value == 2u;
ensures result == 0 implies (counter->value == 0u or counter->value == 1u);
```

It allocates and retires the proof account internally. Its callers need no
ghost parameters or knowledge of the algebra.

### Proof operations need an explicit interface

Pure theorem `apply` currently adds propositions; it cannot perform these
resource transitions. Ordinary `step` follows C execution and should not
pretend an allocation or algebra update is a C call. Proposed notation:

```text
let { authority: ledger, fragment: all } = apply(sum_alloc(0, 2));
let { left: first_part, right: second_part } = apply(sum_split(all, 1, 0));
apply(sum_add(ledger, first_part, 1));
let { fragment: all } = apply(sum_combine(first_part, second_part));
apply(sum_agree(ledger, all));
apply(sum_retire(ledger, all));
```

`sum_alloc(initial, capacity)` returns a full fragment. `sum_split(part,
left_weight, left_amount)` determines the right fields by subtraction and
checks positivity/nonnegativity. `sum_add` preserves its two named binders
with fresh field observations. Combine creates one new binder. Agree adds
`ledger.total == all.amount` while preserving ownership. Retire consumes both.

For example, Add's resource contract has the following clauses, where `delta`
is an explicit nonnegative `Integer` proof argument:

```text
owns ledger: sum_authority();
owns part: sum_fragment();
requires ledger.group == part.group;
requires delta >= 0;
ensures ledger.group == old(ledger.group);
ensures ledger.total == old(ledger.total) + delta;
ensures part.group == old(part.group);
ensures part.capacity == old(part.capacity);
ensures part.weight == old(part.weight);
ensures part.amount == old(part.amount) + delta;
```

Split instead has `consumes part: sum_fragment()` and two named `produces`
outputs. Its postconditions relate their groups to `old(part.group)` and
their weights/amounts to the consumed input. All these clauses require the
checked algebra rule behind them; a contract's text is not its proof.

This proposes resource-transforming lemma application and named results on
`apply`, a real semantic and grammar extension even though it adds no keyword.
Reuse the named input/output discipline of contracts. Initially the named
operations have fixed checked kernel rules; accepting arbitrary declarations
as trusted resource lemmas is expressly excluded. General user-proved resource
lemmas may follow once they have a certificate checker.

The concrete review items are therefore **two algebraic resource interfaces,
`GhostId`, and resource-transforming `apply`**. Nested authority transport and
dependent identity arguments are implementation capabilities behind those
interfaces. There is no resource-description templating, new mutex clause,
surface continuity witness, or arbitrary algebra-definition language here.

## Proof outline for the unchanged C

1. After the parent's existing assignment of zero, allocate `A(g,0)` and a
   full zero contribution with capacity two. Split the fragment into two
   weight-one, amount-zero instances. Fold `P(p,g)` from the actual memory and
   authority. Mutex initialization consumes that wrapper on success and leaves
   it available on failure, following the runtime's branch-sensitive transfer.
2. Each successful create transfers one fragment and a checked mutex-use loan
   to its worker. Failed creation retains both in the parent. The selected
   worker contract carries the same group through its fragment and protected
   resource association. Neither resource identifies the current total.
3. Lock returns the guard and a freshly observed `P(p,g)`. Its total is
   arbitrary subject to the invariant and algebra validity. Unfold exposes
   the actual memory and authority. Step the existing increment, apply Add
   with delta one to authority and worker fragment, and prove the modulo
   relation. Fold the restored state and unlock with state and guard.
4. The worker returns its updated fragment and use loan. Ordinary call/return
   checks establish its `+1` guarantee. The update already happened in the
   critical section; returning does not perform another update.
5. Join transfers that worker's fragment back once. It does not repeat Add or
   change an authoritative total. After all successful workers join, combine
   their returned fragments with any fragment whose create failed.
6. Recover the protected state through destruction after all lifetime/use
   obligations are satisfied. Unfold, compare authority with the full
   fragment, prove the C result, and retire the ghost resources. On init
   failure, use the retained original state instead of destruction.

Memory ownership belongs directly to `P`, not to fragments. Temporary failure
of its equality between the C step and ghost update is confined to the open
protected state; unlock cannot occur until the equality is restored. An
ordinary helper can receive the exposed memory/authority and fragment through
normal contracts. The accounting primitive knows nothing about mutexes.

| Frozen C path | Collected fragments `(weight, amount)` | Exact total after agreement | C result/value |
| --- | --- | --- | --- |
| Mutex init fails | `(1,0)`, `(1,0)` | 0 | `0 / 0` |
| First create fails | `(1,0)`, `(1,0)` | 0 | `0 / 0` |
| Second create fails, first joins | `(1,1)`, `(1,0)` | 1 | `0 / 1` |
| Both create and join | `(1,1)`, `(1,1)` | 2 | `1 / 2` |

A first join alone yields only its contribution. The other worker may already
have run; neither total one nor unchanged memory follows. Reverse join order
must give the same combined result. Runtime assumptions remain those of
`modeled-pthread`, including the lock/join/destroy behavior used by the frozen
program; this proposal adds no native-runtime or termination proof.

## Why this is the Iris pattern, and where it differs

The lock reference is Iris's
[spin-lock specification](https://plv.mpi-sws.org/coqdoc/iris/iris.heap_lang.lib.spin_lock.html):
acquisition supplies the protected assertion and an exclusive lock token;
release requires both back. That assertion can contain accounting ownership
alongside memory. Click's existing use loans and destruction rights remain
additional lifetime obligations; the Iris interface cited here has no destroy
operation. Correspondence is a design discipline, not an inherited soundness
proof for Click.

Our adaptation chooses full exclusive authority, integral shares of an
allocation-selected capacity, nonnegative sums, and checked additive updates.
It does not expose arbitrary cameras, fractional authority, recursive ghost
state, invariant masks, or logically atomic specifications. Natural ghost
totals are related to finite-width C memory by the explicit modulo fact.

Fixed capacity limits later subdivision: with capacity two, a weight-one
share cannot be split again into positive integral shares. A caller that
knows it needs `K` participants can allocate capacity `K`; arbitrary dynamic
subdivision would motivate rational shares later. This algebra alone does
not supply lock-free atomic invariants, termination, fairness, or resource
algebras for ownership of maps and graphs. Those remain separate extensions.

Why not the other candidates:

| Candidate | Assessment |
| --- | --- |
| Retained `remaining(p)` unit grants shared-body authority | Hides the missing unique permission; keep current sequential semantics but stop extending this as the concurrency mechanism. |
| Plain authoritative natural total plus consumed fragments | Partial fragments provide bounds. Absence of a fragment does not establish an exact total of zero. Needs another conservation/completion mechanism. |
| Authority over pending/completed pairs with exchanged receipts | Can support the counter, but adds a second accounting component and a fixed-capacity invariant. Fractional contributions give a more direct existing reference. |
| Fractional authoritative sum | Recommended: one total, split participation, exact agreement after recombination. |
| User-defined arbitrary algebras | Useful long-term direction; adds composition/validity/update proof obligations and their checker before this example needs them. |

## What simplifies, what stays, what remains work

| Existing mechanism | Consequence of this proposal |
| --- | --- |
| `count(R)` for ordinary populations | Keep its current meaning and tests. It is not the new authority's total, the fragment's amount, or its weight. The counter no longer uses it. |
| Retained third unit and whole-population cleanup for the counter | Replaced by full-share agreement and retirement; zero total is valid without a sentinel unit. |
| Scope-close consumption | Still useful for existing sequential population proofs; unnecessary in this counter. Add is explicit before refolding. |
| Pending Count totals and join effect reconciliation | Keep for existing abstract-population clients. The new counter uses ordinary returned resources; no new shared Count reconciliation branch is needed. |
| Population-body custody under a mutex | No new shared-population custody rule for this milestone. Memory and explicit authority are children of the existing protected resource. |
| Mutex association, guards, lifetime loans, observation freshness | Retain. Implement nested opaque resource transfer without fabricating authority or changing group identity. |
| Thread confinement | Keep current restrictions on memory-backed populations. Give the new algebraic atoms checked transfer rules; do not globally relax confinement. |

These are removals from the counter's dependency path, not authorization to
delete working population features. After the milestone, inventory actual
users before any deprecation. In particular, do not silently change `count`
to mean a lower bound or an authoritative field.

The implementation is still substantial: protected-payload refresh currently
accepts a restricted leaf definition, and function/worker transport must carry
the new resources and ghost identities through wrappers. A larger definition
registry alone does not implement custody. All admissions (entry, fold/unfold,
helpers, runtime summaries, and joins) must preserve actual ownership and the
algebra's validity. Ghost fields must not get the ordinary freely refoldable
semantics of a resource containing only model facts.

## Failure explanations and hostile examples

Use the proposed source vocabulary in failures, with the selected binder and
observed values. For example:

```text
Requires owns ledger: sum_authority()
Requires ledger.group == part.group
Requires all.weight == all.capacity
Requires left.weight + right.weight <= left.capacity
Requires to_integer(p->value) == total % 4294967296
Requires part.amount == old(part.amount) + 1
```

Separate an unsupported interface from an unproved requirement. Do not report
an algebra implementation subsystem as the missing premise.

Required negative cases include:

- Fold or construct authority from only a group name or pure field facts.
- Put the same authority inside two wrappers or two mutexes.
- Add with a fragment alone, a view, the wrong group, or a stale instance.
- Duplicate a zero-contribution positive share; combine beyond capacity.
- Change a contribution without the matching authoritative update, or update
  the ghost total without the matching C increment before restoring `P`.
- Double the C increment under a worker contract promising contribution `+1`.
- Discard a fragment and claim that full-share agreement or retirement holds.
- Reuse an old acquisition's total as the total after interference.
- Join twice, return the same fragment to two parents, or repeat an update at
  join. A legitimate second Add while actually holding authority is not an
  algebra error; a `+1` worker contract must reject the resulting `+2` effect.
- Use another account at the same pointer, or change group on reacquisition.
- Destroy the mutex before loan recovery, even if some arithmetic fact is known.

## Implementation sequence after review

1. Check the restricted algebra rules and fresh identities independently of
   mutexes. Implement allocation/split/combine/Add/agreement/retirement and
   their certificate forms; compare each with the stated Iris correspondence.
   Verify ordinary wrappers and helpers, including an unsigned-wrap bridge.
2. Add the reviewed surface interface and general transport of the opaque
   children. Verify that protected acquisition refreshes observations while
   preserving the same group and exclusive authority. Keep old counted-body
   refusals in place.
3. Verify the unchanged worker and parent, all failure cleanup paths, and a
   separate reverse-join-order regression. Prove success implies value two;
   prove exact zero/one cleanup observations on the individual failure paths.
4. Expand, reverify, and audit the proof; run `scripts/check.sh`. Add
   deterministic scaling checks varying unrelated groups, definitions, and
   resources. Operations must use selected binders and persistent indices,
   not scan all workers or fragments to calculate a total.

The design-phase result is a proposed semantic interface and proof argument,
not a checked algebra formalization or successful concurrent proof. Review the
surface choices above before implementation; no parameter scaffolding or
parser keywords are added by this document.
