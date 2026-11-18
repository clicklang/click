# Exact reads: a Surface form for off-version reads

Status: approved (E1-E4, 2026-11-18). Step 1 (the Surface form) is implemented; steps 2-4 are not.

## Problem

A Click read of a place lowers to the read at the cell's **version point**: the
memory state that the assumption-free version walk selects
(`docs/internals/raise-lower-principle.md#a-read-names-its-version-point`).
Normalizing onto the version point is subtle, so the kernel does it once, when
evaluation first reads the code. It does not re-normalize between proof steps.

The kernel also holds **off-version reads**: reads named by a memory state that
is not the version point of their cell. They are valid kernel terms.

- Substitution, rewriting and transport move terms without re-running the walk.
  The equality graph relates partial terms; it never re-normalizes a read
  when another term in its class changes.
- Some evaluation paths name a read by the exact state it was taken in. For
  example, `Pointer::from_read` gives a loaded pointer the read at the exact
  memory as its provenance and bounds owner.

The raise-lower principle requires every term a proof state holds to raise to
Surface text that lowers back to it. Today no Surface text lowers to an
off-version read: `p[i]` and `at(point, p[i])` both lower through the walk. So
any fact that contains an off-version read either raises to text naming a
different read (`differs`) or does not raise (`unraised`).

The raise-lower audit (`scripts/raise-lower.sh`) measures this for pointer and
address facts that have a state to raise at. On master `74990f08` (before
#3270):

| outcome | count |
| --- | --- |
| same | 531 (33.7%) |
| differs | 317 (20.1%) |
| unlowered | 90 (5.7%) |
| unraised | 595 (37.8%) |

Term dumps of the `differs` cases show the same pattern. The address names the
version-point read, but the pointer's provenance names the read at the exact
state. Both are correct kernel terms; the second has no Surface spelling.

## Proposal

Add one Surface form, `exact(place)`: the read of `place` in the state in
scope, named by that state, with no version walk.

| Surface | Lowers to |
| --- | --- |
| `p[i]` | the read at `p[i]`'s version point from the current state (unchanged) |
| `at(point, p[i])` | the read at `p[i]`'s version point from `point` (unchanged) |
| `exact(p[i])` | the read of `p[i]` named by the current state itself |
| `at(point, exact(p[i]))` | the read of `p[i]` named by `point`'s state itself |

`exact` takes any place expression: `exact(h->next)`, `exact(a[i].f)`. The
read's type and width come from the place, as they do for an ordinary read. It
is legal wherever an ordinary read of that place is legal, and nowhere else.

`exact` applies to the outermost read of its place only. The reads that compute
the place's address stay ordinary unless they are wrapped too:
- `exact(p[i]->next)` reads `->next` exactly, through the version-point read of
  `p[i]`;
- `exact(exact(p[i])->next)` reads both exactly.

This keeps the form compositional, and raising wraps exactly the reads that
need it.

`exact` is a built-in call form, like `old` and `address`. One mdtest,
`integer_arithmetic_compares_an_integer_function_with_a_machine_value.md`,
declares a function named `exact`; that test-local name is renamed.

Both forms denote the same value at the same state. They differ only in which
kernel term names that value. The two are related in the equality graph the
same way they are today, by the fact-free version walk. `exact` grants no
access permission and adds no facts.

### Why a new form and not a reading of `at`

`at(point, place)` already means "read `place` as seen from `point`", which
normalizes. Making `at` sometimes mean "exactly this state" would make its
meaning depend on how the text was produced. `exact` composes instead:
- `at` chooses the state;
- `exact` turns off normalization;
- neither changes the other's meaning.

`read` would be the obvious name, but it is a built-in resource name
(`read(p[0..n])`); the validator refuses declarations named `read`.

## Lowering

- Ordinary reads are unchanged.
- `exact(place)` lowers the place's address as usual. It then builds the read
  at the exact memory of the state in scope, with the same constructor
  evaluation uses for that state, and does not call the version walk.
- For an integer cell this is `MachineTerm::MemoryLoad(ProgramPoint::at(state),
  address, kind)`. Lowering skips `canonical_scalar_read`.
- For a pointer cell this is `Address::loaded_value(state.unchanged_bytes_source(), address)`.
  An exact pointer read is named by the state's unchanged-bytes source, as
  `Pointer::from_read` already names provenance: a step that changes only
  cached knowledge, not bytes, keeps the read's identity. The
  value is built with `Pointer::from_read`, so its provenance and bounds owner
  are the same exact read. This is what evaluation produces, so the two agree.

Lowering stays fact-stable. `exact` reads no facts, and the term depends only
on the place and the state in scope.

## Raising

The raiser chooses between the two forms by identity. It never tries a
candidate spelling and falls back to another.

1. A read whose memory is the version point that the walk selects for its
   place, from a recorded state at `point`, raises as `at(point, place)`, or as
   `place` at the current state. The raiser checks this with an indexed lookup,
   not a walk. Evaluation records `(producer state, place) -> version-point
   read` when it names a read (branch `raise-version` has this registry and its
   scaling test).
2. Any other read raises as `at(point, exact(place))`, where `point` names the
   read's own memory state.
3. A pointer's provenance and bounds owner are not raised separately. Lowering
   rebuilds them:
   - an ordinary read uses the version-point read;
   - `exact` uses the exact read.

   So a pointer value whose address and provenance disagree in kind cannot
   round-trip under either form. Evaluation must not mint one (see step 2
   below).

## The pointer provenance rule

Today a pointer read minted during evaluation has:
- the version-point read as its address (since #3270), and
- either the version-point read (via `Pointer::new`) or the exact read (via
  `from_read`) as its provenance, depending on the path.

That mix is the main source of pointer `differs`.

The rule becomes: **a pointer read's provenance and bounds owner are the same
kind of read as its address.**
- A read named at its version point has version-point provenance.
- An `exact` read has exact provenance.

`from_read` keeps its exact-state behaviour for exact reads. The
version-point form gets the version-point read. This is the same walk lowering
already runs, so it is not a new historical search.

An earlier experiment moved all provenance to the version point, which is the
version-point half of this rule. It still passed
`a_loaded_pointer_cannot_reach_storage_created_after_the_read`. The experiment
started the walk from the read's own memory. A variant that started from the
unchanged-bytes source failed it, because adding an object changes no bytes,
so the walk stepped back past an object's creation. The rule must keep that
test passing.

## States with no program point

Rule 2 needs a program point for the read's memory. Two kinds of state seen in
the audit have none:

- **Projections for one read** (`<state A>` in diagnostics). These are built by
  load canonicalization, and their single source is recorded
  (`record_canonical_load_projection`). They are part of the normalized form,
  so a read at a projection raises under rule 1, not as `exact`. The `differs`
  that show `<state A>` were caused by the provenance mismatch, not by the
  missing name.
- **Other intermediate states**, such as within a statement or "a memory
  derived from another state for one read". If an off-version read is named by
  one, rule 2 has no point to write. To be measured after steps 1-3. If any
  remain, the options are to name the state where it is created, or to
  record its nearest program point. Both follow the principle's instruction to
  name the value where it is introduced.

## Steps

Each step is one PR, measured with the raise-lower audit and
`scripts/fact-stability.sh`.

1. **The Surface form.** Parse, validate and lower `exact(place)`, and print it.
   Add mdtests:
   - an `exact` read lowers to the state's own read;
   - an `exact` read equals the ordinary read where the walk is trivial;
   - `exact` grants no access.

   No raiser change yet.
2. **One provenance kind per pointer read.** Make evaluation and lowering apply
   the provenance rule above. Fix the tests that pin the old mix; on the trial
   branch these were:
   - `generic_stack` `pop`;
   - the cached-pointer tests in `memory_loads`;
   - packed-word transport;
   - two pointer-naming scaling tests.

   Each is checked against the rule, not just updated.
3. **Raise by identity.** Add rules 1 and 2 to the raiser, using the recorded
   version-point registry. Re-run the audit; `differs` for pointer facts should
   fall toward zero, with `unraised` limited to the no-program-point states.
4. **No-program-point states**, if step 3 shows any remain.

Separately, and first: `ConditionTerm::pointer_equal` should route a comparison
with null to `address_equal`, as lowering of `p == 0` already does. This is
independent of everything above and correct under either naming. It removes
about 30 pointer `differs` (`0 == p` raised, `p == 0` lowered). Two
`complete_pointer` tests pin the old term and need their expectations
updated.

## Decisions

Approved 2026-11-18.

- E1. The form is named `exact`.
- E2. `exact` takes a place expression (`exact(p[i])`), not `read(p, i)`.
- E3. A pointer read's provenance and bounds owner are the same kind of read as
  its address: version-point for an ordinary read, exact for an `exact` read.
- E4. `exact` appears in user-facing output: raised proof text, `click expand`
  output and diagnostics. Authors may also write it.
