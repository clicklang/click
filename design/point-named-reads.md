# Point-named reads: one name, and the relations it needs

Status: approved (2026-11-23). P0 is implemented. P1 has begun: logical
integer reads ask `ProgramPoint::read_version`.

## Problem

The program-point migration (`roadmap/smart-tactics.md`, "Program-point memory
migration") moves reads from names keyed by a memory snapshot to names keyed
by a program point, and then deletes the legacy snapshot walk
(`resource_tracker::last_same_version_point`). Slices so far have each taken one
narrow read shape. A general slice does not survive the test corpus.

The general slice tried on 2026-11-22: a read of a caller cell at a symbolic
offset is named at the start of the recorded suffix in which every step left
caller storage alone. It was selected inside the shared entry selectors, so
every producer that asks for a caller cell's version got the same answer. The
legacy walk cannot cross such a write for a symbolic offset either, so the
version is the same place the walk stops. On the gate harnesses (local branch
`codex/caller-storage-reads`):

| variant | examples failing | mdtests |
| --- | --- | --- |
| master | 0 of 59 | pass in about 9 minutes |
| suffix version | 20 of 59 | 78 failed; the harness hit its 20-minute limit after 5,872 of them |
| suffix version, skipped when the memory holds the cell | 14 of 59 | not run |

Almost every failure is a frame step: "this value is unchanged across that
store or call". Either `known` does not find a premise that prints like the
goal, or the implicit tail exhausts its budget on that question.

The cause is not the rule. Today a read can be named in three ways, and each
relation proofs depend on was written for one of them. Renaming a read class
removes it from the relations that held it.

## How a read is named today

1. **By a value the memory holds.** A memory state caches cell values. A read
   of a cached cell is that value, and a cell holding its own earlier read is
   that read (`docs/internals/raise-lower-principle.md#a-read-names-its-version-point`).
   This is what keeps a field one term across a loop head or a disjoint call:
   the memory carries the term forward. It costs nothing per read.
2. **By the legacy walk.** A read of an uncached cell is named at the oldest
   memory state the assumption-free walk reaches. It is keyed by that state
   (`ReadKey::Memory`). Two paths with equal memory share the name.
3. **By a program point.** The point indexes (`program_point.rs`: indexed
   writes, call outputs, function entry, the entry-writes record, static and
   array versions) select a version, keyed by point (`ReadKey::Point`).

Producers pick among these in different orders. The C read path selects an
entry version before it looks for a cached value (`eval/expression.rs`, the
`entry_read` choice ahead of `evaluate_retained_memory_load_paths`). Logical
reads look for the cached value first and drop their point for integers
(`evaluate_logical_memory_load_paths_at`). Resource-body lowering names fields
at the resource's source point. A quantifier rename rebuilds reads from bare
memory (`reasoning/substitution.rs`; it now keeps entry and exact selections).

## The relations proofs depend on

| | relation | works for memory-named reads by | for point-named reads today |
| --- | --- | --- | --- |
| R1 | the same cell is one term while it is cached | the memory carrying the term | bypassed when a selector runs before the cached-value lookup |
| R2 | a read across a step that facts prove separate equals the read before it | the memory DAG under facts (`memory_load_equality_evidence_at`, `LoadCellWalks`) | the walk takes memories, which point reads carry; candidate selection and its cost are unverified |
| R3 | exact lookup: a goal finds a premise spelled the same | fact keys and comparison forms; the equality graph's projection edges | point reads are their own comparison identity, and projection edges are skipped for them (`register_logical_read_values`, `pointer_domain_read_key`) |

R3 holds whenever both producers chose the same version. It breaks only on
mixed names, which the census `kernel::mixed_read_names` reports. On master it
reports 53 cells in 49 mdtests, from 6 producer lines. R1 and R2 are where a
rename turns a free equality into a proof obligation, or into search.

## Proposal

### P0. One constructor for read terms (implemented)

Read identity had no owner: integer read terms were built directly at 69
non-test sites in 26 files, and the mixed-name census could attribute a read
only to the first code that built a bare point for its memory, which is not
always the code that built the read. Every integer read term is now built by
`MachineTerm::read_named(point, pointer, kind)`, or by
`MachineTerm::memory_read(memory, ..)` for the legacy memory name.
`build_support/read_construction.rs` holds other direct
`MachineTerm::MemoryLoad(..)` constructions outside test code to zero, so the
rule cannot erode. Both constructors take `#[track_caller]` in test builds:
the census can name the producer exactly, and a change to how reads are named
has one place to go. The other read representations
(`AlgebraicTermNode::MemoryLoad`, `KernelTermNode::MemoryLoad`) get the same
treatment when a slice reaches them.

### P1. One selection function, in one order

```text
A producer names a read in this order; step 2 is ProgramPoint::read_version:
  1. the value the memory holds for the cell (R1), if any
  2. the point indexes' version, if any
  3. the legacy walk (counted by `click audit legacy-walk`)
```

Every producer calls it: C reads, logical reads, resource lowering, folds,
substitution, and canonicalization of an existing read. Today each runs its
own cascade at its own place in that order. That is where both the mixed names
and the R1 breakage come from. Step 1 first preserves the mechanism that keeps
most frame steps free. The 20 → 14 result above is the evidence that it
matters. A slice then changes only step 2's coverage. The legacy walk shrinks
when step 2 answers more, and is deleted when step 3 is unreachable.

This is not behavior-neutral. A producer's order is tied to more than naming:
- **Definedness.** The C read path's early entry selection refuses a
  materialized entry view (`entry_integer_version`). Moving it to
  `read_version`, which accepts one, let an owned but uninitialized cell skip
  its definedness refusal (two `owns_uninitialized_*` mdtests).
- **Cost.** Moving that selection after the evaluator's resolution steps kept
  every mdtest green but raised legacy-walk work on `examples/` by 17%, since
  those steps run the walk first.

Each producer moves with its checks, and with its legacy-walk work measured
before and after. Logical integer reads moved first
(clicklang/click#3982), with no change in walk traffic.

### P2. R2 for point-named reads: one hop, checked in the querying context

When a point-named read at version `S` meets a read of the same cell before
`S`, relate them when `S`'s own recorded step is proven separate from the cell
under the querying path's facts. The step is a store, a checked call or a loop
footprint. The check is `step_effect::affects` with those facts, the rule the
legacy walk already uses. On success the read at `S` equals the cell's version
at `S`'s predecessor, selected by P1.

It is one hop per question, like `memory_dag_cell_source`. A longer chain is
written as `have` links, as today. Nothing is recorded on the shared edge,
which stays assumption-free. The hop is asked where R2 is asked now: candidate
pairs from fact matching (`memory_loads_proven_equal`) and the
frame/`preserve` tactics. It is never asked by scanning reads.

### P3. R3 needs no new mechanism

With P1, two producers of one cell at one point produce one term, and exact
lookup works as it does for memory names. The projection edges that point
reads skip exist to relate memory-named reads to their projection sources.
They go away with the legacy walk.

## Design check

```text
Design check
- Part: Memory (fast). P1 changes evaluation order, not search.
- Why this part: every evaluated read is named here.
- Fast: P1 reads the cell store (indexed), then the point indexes (indexed
  lookups already in place), then the legacy walk (unchanged and counted).
  P2 is one `affects` check on one recorded step per candidate pair, with the
  pair supplied by existing candidate selection; no new index.
  Scaling: P2 must cost the same as the history before `S` grows
  (deterministic work at 4 / 64 / 1024 unrelated steps).
- Fact-stable: P1 reads no facts. The cell store is memory, not facts. P2
  runs in checking, never during lowering.
- Failure: P1 falls back to today's route. P2 failing leaves the two reads
  unrelated, as for a memory-named read whose walk stops; the proof states
  the frame explicitly.
```

## Plan

0. **P0.** One constructor and the construction ratchet. Then attribute the
   census at the constructors and recount the corpus.
1. **P1, no new coverage.** Route producers to `read_version`, one producer
   per commit. Exit: both harnesses pass, legacy-walk work on `examples/` does
   not rise, and the census count does not rise.
2. **P2.** Add the hop, with a scaling test and the `dfs` and `bounded_pool`
   frame steps as regressions. Exit: harnesses pass.
3. **Coverage slices.** Re-apply the caller-storage suffix version, then
   loaded-pointer and heap storage, as step-2 entries. Exit per slice: the
   harnesses pass and the `click audit legacy-walk` count falls.
4. **Delete the walk** when step 3 of `read_version` is unreachable on the corpus.

## Open questions

- P1 step 1 keeps cached values ahead of point versions. A cached value can
  outlive its point version only by being carried, which is the point of R1,
  but raising must still name it. Check that every cached read still raises to
  `at(point, place)` or `exact` (`design/exact-reads.md`).
- Whether P2's hop should also cross a loop footprint, which the naming walk
  never does (`raise-lower-principle.md`: a loop havoc keeps two names). The
  conservative answer is no: keep loop frames explicit.
