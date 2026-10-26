# Smart tactics: four engines, and simple tactics with elided arguments

Priority: P1.

Soundness: not soundness. Every route applies kernel-checked steps, and an
answer from search is still checked. The cost is comprehensibility,
predictability, and the ability to recover from slow search: some search hides
inside tactics that are classified as simple, and some smart searches have no
syntax that records their result, so `click expand` cannot remove them.

P1 by user direction (2026-10-20).

## Principle

Slow work happens in only two kinds of places.

1. **Four smart tactics: `simp`, `arithmetic`, `execute` (with
   `execute_until`), and `auto`.** Each one expands into other tactics. They
   nest: `arithmetic` is the arithmetic engine, `simp` simplifies and hands
   arithmetic subgoals to `arithmetic`, and `auto` runs `execute` and then
   `simp`. `execute` and `auto` are thin wrappers over fast checking, the other
   engines, and the helpers below.
2. **Search helpers that fill an elided argument of a simple tactic.** A
   helper finds a fact, a premise list, a resource instance, or a quantifier
   instance. Expansion writes the found value into the same tactic and does not
   replace the tactic. A helper is valid only if its result is an argument that
   an existing simple tactic accepts.

Everything else is simple: deterministic, near-linear checking with no search.
A tactic such as `apply`, `transport`, `step`, or `fold` is a simple core,
possibly with elided arguments. It does not run `simp` or `auto` itself. A
`step` or `fold` leaves the obligations its fast path does not settle to the
implicit `auto`, as it does today.

The kernel's condition decision (`PureFactContext::decide`) is part of fast
checking, not search. Simple tactics may use it.

A tactic may also be **sugar**: a fixed expansion, with no search, into a call
of one of the four engines. Bare `close_invariants()` is sugar for
`close_invariants() by { … }` with `simp()` on each invariant member. A
tactic that tries "whatever proves it" is not sugar.

**The north star:** every elided argument can be written explicitly. Once it
is written, no helper runs.

Two consequences follow:

- Every search has syntax for its outcome. However slow or heuristic a search
  becomes, its result can be written down and checked without searching.
- Checking that written outcome is fast. If expanded proofs are slow, expansion
  rescues nothing, so the simple layer has to meet the complexity contract in
  [verification efficiency](../docs/internals/verification-efficiency.md).

## Current state

The facts below come from code audits of `master` on 2026-10-20.

### Smart tactics today

`SmartTacticKind` (`src/surface.rs:4211`) had eight kinds:

- the four engines: `Simp`, `Arithmetic`, `Auto`, and `execute` as two kinds
  (`SmartExecute` and `ExecuteUntil`);
- `ApplyTheorem`, which covers both `apply(theorem(args))` and `apply(ih(m))`;
- `FactTransport`;
- `CloseInvariants`.

It now has the four engines (`Arithmetic`, `Simp`, `Execute`, `Auto`); see
step 12.

The engines are not layered as the principle says:

- **There are five arithmetic engines, not one.**
  - the signed planner (`checking/signed_arithmetic_planner.rs`);
  - the Integer-affine planner (`checking/integer_affine_planner.rs`);
  - the special pointer/float planner (`checking/special_arithmetic_planner.rs`);
  - simplex refutation (`checking/integer_refutation_planner.rs`), which only
    `auto` uses;
  - the kernel's atomic decider.
- **`simp` calls three of the planners itself**, with bound selection that
  `arithmetic()` lacks. So `simp` is stronger at arithmetic than
  `arithmetic()`. The special → affine → signed sequence is copied four times:
  in `simp`, in `simp using`, in `arithmetic` (`step_application.rs`), and in
  post-execution `arithmetic using` (`claim_proofs.rs`).
- **`auto` owns engines of its own** (`proof/selected_arithmetic.rs`,
  `smart_closures.rs:2330`):
  - simplex and its bridged, machine-goal, equality-by-bounds, and definedness
    variants, several of which call `auto` recursively;
  - a 16-rewrite pass on a single connected equality;
  - a depth-3 rewrite chain;
  - definition-condition reading;
  - constructor join.

  `auto` runs `simp` first and then the solver after execution, but runs the
  solver first for a stated `have`.
- **`close_invariants()` has its own premise selection** (`named_arithmetic_premises`),
  a walk over the invariant bundle, trimming of signed-planner premises, a
  `normalize() using` fallback, and a closer for universal invariants
  (`execution_statements.rs:250-760`).
- **`apply(theorem)` searches its premises with a cascade**
  (`smart_execution.rs:479-900`) and then proves each missing premise with
  full `auto`. `apply(ih)` proves its missing premises with `simp`.
- **Bare `transport(P, Q)` plans over every available fact**
  (`plan_explicit_fact_transport`) and then minimizes the result by deletion.
- **Premise selection is a grab bag of four unrelated selectors**:
  `arithmetic_connected_premises`, `simp`'s indexed bound selection,
  `named_arithmetic_premises`, and the transport planner.

### Simple tactics that search

| Tactic | Hidden search | Where |
|---|---|---|
| `assumption()` | On an outcome goal it checks the snapshot-blind bucket: the same proposition at other snapshots, each by a memory-DAG proof that its loads are unchanged. Measured (step 14): at most 2 candidates, and `assumption` closed 7 goals this way, each from one candidate. No search; the docs now say what it accepts. | `kernel/proof/object.rs:626`, `facts.rs` (`exact_available_across_effects`) |
| every `using` list | A premise is matched against facts at other snapshots by the same bucket and proof. Same measurement: no choice to cite. | `facts.rs` (`listed_premise_available`) |
| `extract(P)` | Finds the source implication or disjunction by consequent. Already indexed (step 14): one lookup keyed by the written `P`. | `facts.rs` (`contains_discharged_implication_consequent`), `object.rs` (`apply_extract`) |
| `fold` / `unfold`: choosing the instance | Finds a held fact that entails the requirement, through pointer roots linked by equalities and memory subranges. Measured (step 14): at most 3 indexed candidates, and where two match the required fact itself is chosen. No citation needed. | `primitives/resource_algebra.rs` (`directly_supporting_fact`) |
| `fold` / `unfold` / `observe` / `open`: the guard | Scanned all `condition_facts` linearly for a fact at another snapshot, then fell back to the general `decide`. The scan is gone (step 14): an exact lookup, then `decide`. | `resources.rs`, `memory_conditions.rs` |
| bare `step()`, `fold`, `open` close | Open obligations go to an implicit `auto`. | `execution_statements.rs:1736,1816-1940` |
| `if` / `cases` / `match` arm choice | `decided_without_search`, which despite its name calls the general `decide`. | `proposition_search.rs:260`, `fixed_state_steps.rs:456,3184,3246` |
| `transport(P, Q) using {..}` | Chooses the instance of a universal premise by scanning facts. | `proposition_reasoning.rs:672`, `fact_transport.rs:1199-1360` |
| `loop` with a verified rule | Automatic fact transport tried every memory fact. Removed (step 14): no fact is carried by search. | `transition_certification.rs` |

`PureFactContext::decide` is accepted as fast checking (see Decisions), so
its uses in `step`, `fold`, and arm choice are not hidden search. That puts it
in the fast part, under the fast-part rule: no scans. Plan step 1 gave each
decision a per-query fuel as a safety net. Probing it with growing related
facts found three shapes that are superlinear in one decision (see
"Fast-part scans").

### Syntax for helper outcomes

| Implicit choice | Syntax | Status |
|---|---|---|
| Premises for `apply` / `apply(ih)` | `apply(t(x)) using {..}` | exists |
| Frame premises for `transport` | `transport(P, Q) using {..}` | exists |
| Arithmetic and normalize premises | `arithmetic() using`, `arithmetic_certificate`, `normalize() using` | exist |
| A fact at another snapshot | `at(mark / function.entry / region(N).entry / loop(N).entry, P)` | exists, but `assumption()` takes no argument, and frame evidence needs a separate transport |
| Instance of a universal | `instantiate(F, v)` | exists as a separate step; `transport` has no instance argument |
| Resource instance | `unfold(name)`, `fold(r, {slot: child})`, `step(c, {b: i})` | partial: no way to name a memory range or cite a held fact |
| Source fact of `extract` | none | missing |
| Guard of a conditional resource body | none: the parser refuses `using` on `unfold` (`parser.rs:9585`) | missing |
| Facts behind a `decide` answer in `step`, `fold`, or arm choice | none | missing (unless `decide` is accepted as checking) |
| Facts a `loop` carries across its body | none | missing |
| Invariant obligations | `close_invariants() by {..}` | exists |

`click expand` already writes `using {..}` into `apply` and `transport`
(`expansion/tests.rs:2984`, `expansion_tests.rs:5397`). However, it writes the
premises `auto` proves for `apply` as `have`s before the `apply`, rather than
leaving them open. It records nothing for the choices made by `assumption`,
`fold`, `unfold`, or `step`, and nothing for the instance inside `transport`.

### Tracing and profiling

- **Traces show the result of a search, not the search.** A trace
  (`src/surface/proof_trace.rs`) shows only the simple steps on the accepted
  path, labeled with the smart tactic's source location. Nothing marks a step
  as having come from `auto`, `simp`, or `execute`. (Step 15 adds that mark
  and a `chosen:` line for a searched `using` list.)
  - A failed search leaves only the checked prefix and the `failed check`
    block.
  - A helper's choice is visible only partly for transport and for call
    spellings. It is not visible for `apply` (theorem, instantiation,
    premises), for instances, or for resource instances.
  - `CheckObservations` covers only written `simp`.
- **The tracing skill (`.claude/skills/tracing/SKILL.md`) and
  `docs/concepts/tracing.md` use the old taxonomy.** They say a link is done at
  "one `apply ... using`", and that a miss by a smart tactic is never a
  `failing-tactic`. They have no rule for a helper that finds nothing.
- **`click profile` sorts every row into SMART, SIMPLE, or CONTROL**
  (`src/surface/proof/timing.rs:37-82`, `src/bin/click-profile/rendering.rs`).
  Under the principle, a slow helper inside a simple tactic would be labeled
  "SIMPLE ENGINE BUG" even though expanding it fixes it.
- **The classification is stored in four places that must agree:**
  `ProofTactic::class()` (`src/surface.rs:4672`), `PUBLIC_TACTIC_FORMS`
  (`src/surface.rs:4250+`), `certificate_step_class`
  (`src/surface/proof_certificate.rs:1016`), and the class column of
  `docs/reference/tactics/index.md`, which `src/docs.rs` parses. A test
  holds them together: `tactic_classification_tests` in
  `src/surface/parser.rs` parses one instance of every public form and
  compares its `class()` with the registry and with its certificate step,
  and `tests/documentation.rs` compares the registry with the reference.
  `refusal_meaning` (`src/docs.rs:71`) has three meanings and needs a fourth
  for a helper miss.

### Documentation

The definition of smart versus simple is repeated in about eight places:

- `docs/concepts/smart-and-simple-tactics.md`
- `docs/reference/tactics/index.md:4-15`
- `docs/reference/glossary.md:51-56,132-135,966-978`
- `docs/concepts/proof-scripts.md:65-98`
- `docs/concepts/proof-failure-triage.md:186-206,299-309`
- `docs/internals/verification-efficiency.md` ("Simple means locally checkable", "Condition decisions in simple checking")

Other docs that need the new taxonomy:

- `docs/concepts/expansion.md`
- `docs/concepts/proof-workflow.md`
- `docs/concepts/profiling.md`
- `docs/concepts/performance-tools.md`
- `docs/concepts/pure-functions.md:243-251`
- `docs/concepts/tracing.md`
- `docs/reference/language/index.md:659-664,1179-1182`
- `docs/reference/language/limitations.md:319-327`
- `docs/reference/cli/expand.md`, `profile.md`, `audit.md`, `docs.md`,
  `verify.md:292`
- `docs/internals/testing.md:586-593,923-948,1161-1360`
- `docs/internals/proof-objects.md:164-191,413-416,506-519`
- `design/smt-auto-stage1.md:362-375`, which is the closest existing statement
  of this model

These contradictions were listed at the audit; step 4 fixed the descriptions
of bare `apply`, `auto`, and the implicit claim closer, and step 17 checked
the rest. `assumption` and `step`/`fold` are now described as lookups and
the kernel's decision, with open obligations going to the implicit `auto`,
and "bare `apply(ih)` is smart" is right under decision 3:

1. **`assumption`.**
   - `tactics/index.md:1221,1263` says it does no search.
   - In fact it recurses into disjunctions, uses equality closure, and matches
     across snapshots.
2. **`step` and `fold`.** At least four places say they "never search", while
   each hands off to the implicit smart `auto`.
3. **"Bare `apply(ih)` is smart"** is stated three times:
   `tactics/index.md:989`, `language/index.md:1179`, and
   `pure-functions.md:249`.

## Fast-part scans

[Verifier design](../docs/internals/verifier-design.md) splits the verifier
into a fast part, which checks, and a slow part, which searches. The fast
part does indexed lookups and work proportional to its explicit input and
output; it doesn't scan. The slow part may scan, but only where `click expand`
can write its result as fast-part steps. This is the same principle as the
smart-tactic one above, applied to the whole verifier: every cost is either
small or expandable.

Each scan below breaks that rule today. Each one has two ways out:

- **Make it fast.** Replace the scan with an index keyed by the operation's
  input, and add a scaling test that grows both unrelated and related input.
- **Make it expandable.** Move the work out of the fast part into a smart
  tactic or a search helper, and give the tactic explicit syntax for what the
  search found, so the explicit form does only a lookup. This is the right
  choice when the scan is really a search for which fact to use.

Which way to take is decided per scan. Most of the kernel scans below have a
natural index; most of the "simple tactics that search" above are better
made expandable.

### Every scan is named

The two main fact collections, `condition_facts` and `prop_facts`
(`FactMap` and `FactSet` in `src/kernel/fact_collections.rs`), have no
plain iterator outside tests. Every loop over a whole collection names its
kind, so the compiler lists every scan and a new one cannot be written
without classifying it:

- `scan_for_upkeep()`: maintaining the context itself, such as rebuilding
  an index after a withdrawal, recomputing its fingerprint, copying it
  whole, a debug consistency check, or rendering a diagnostic after a step
  failed.
- `scan_explicit_input()`: the context is a step's own premises, for
  example the premises a certificate names, so the work is the size of
  input someone wrote.
- `scan_for_search()`: a search that `click expand` replaces with explicit
  steps. Today these are the `simp` scans in
  `condition_reasoning/simp.rs`, each reached only from
  `decide_condition_for_simp`.
- `scan_unindexed()`: fast code that reads every fact. Each use is a bug
  in the list below, and the count of uses goes down to zero.

The fast/slow line is expansion: anything that still runs while checking an
expanded proof must be fast. That is every simple tactic and every kernel
check, not only code outside `simp`.

Proposition facts (`FactSet`) have no `scan_unindexed` at all now: fast
code reads them only through an index, and a new whole-set scan there does
not compile.

**Known fast-part scans** (`scan_unindexed`) still open:

- The memory-resolution condition match's fallback
  (`scanned_matching_condition_fact_for_memory_resolution`), reached from
  `functions.rs` and contract certification whenever its index declines.
  It matches up to memory-resolution equality, which no key spells, and
  `mdtests/call_step_retains_old_array_bound.md` needs it: the call's
  `0 <= old(left[cur])` requirement holds by a fact about the same cell at
  another snapshot named through an equality.

**Fixed: the exact check is exact.** Measured across the gate, the
condition scan `settles_exactly` fell into (`proves_condition_from_facts`)
ran 18,636 times in fast code and found a fact 27 times, none of which a
gate proof needed. `proves_atomic_without_search` now answers a condition
by lookup in an ambient context; the full match, through reasoned
equality, conjuncts, implications and universal instances, is
`proves_atomic_from_premises` over a context that is a step's explicit
premises, as derivations and their checks are, and
`proves_condition_from_facts` for the proposition search. The `ForAll`
goal's alpha match compares operands by lookup too.
`exact_condition_check_ignores_unrelated_implications` covers it.

**Fixed:** equality and snapshot walks.
`bitvector_terms_equal_from_snapshot_facts` chained stated equalities
through snapshot-aware endpoints over every condition fact at every step;
it ran 6,956 times across the gate and never matched. A stated equality
is an equality-graph edge already, so only the loads' own snapshot
comparison remains. The chain walk in
`pointer_offsets_equal_with_resolved_atoms` is gone for the same reason.
`has_pointer_offset_snapshot_fact` reads the offset equalities filed
under the query's snapshot shape (`offset_snapshot_shape`: structure with
each load as its kind, sums in either order), which every
snapshot-equivalent side shares. `nonnegative_successor_by_exact_facts`
reads the order facts filed under the term's canonical form. An assumed
existential alpha-equal to the goal is read from the goal's identity
bucket of the stated-proposition index (`stated_identity_bucket`).
`offset_and_existential_matches_ignore_unrelated_facts` and
`successor_rule_ignores_unrelated_condition_facts` cover them.

**Fixed:** the exact order walks. `exact_signed_order_path_evidence`
and `exact_wide_order_path_evidence`, used by the resource tracker during
execution, collected every condition fact per call, and
`has_exact_order_path` collected every order fact at a constant or load
node. They read `OrderFactsByLower`, which files each order fact under its
written lower end, a constant lower end by value (one range read finds
every constant at least as large), a load lower end by pointer and kind,
and a 64-bit fact by canonical lower end. The evidence walk visits the
candidates in the order the scan did, so it returns the same path;
`indexed_evidence_walk_finds_the_scanned_path` checks that, and
`constant_order_walks_ignore_unrelated_order_facts` the scaling.
`condition_order_facts` now serves only `simp`.

Where a match is up to an equivalence that implies equality of a
computable key, such as a canonical form or a snapshot shape, an index on
that key keeps every verdict and reads only the candidates.

**Fixed: universals are read by conclusion shape.** Each universal fact
is filed under the shapes its conclusion takes (`UniversalConclusionKey`:
an `int32` equality, a strict or non-strict order, an overflow, an integer,
pointer value or offset equality, loadability, or another condition),
read through its binders, implications and conjunctions. Two conditions
`condition_matches` relates share a shape, and so do alpha-equivalent
propositions and propositions equal up to proven terms. So these read only
the universals under their goal's shape: instantiation for a derivation
(`select_forall_int32_instantiation_evidence`), certification of a
condition (`condition_holds_by_instantiated_fact`) and of a loadable cell
(`quantified_int32_fact_certifies_loadable_cell`), the alpha match of a
universal goal, and the consequents an iterated guard equality
instantiates (`instantiated_universal_consequents`, which takes the
equality's two sides: its one caller, the iterated guard, asks only an
equality, and another condition would offer its own variables to every
universal). Universal facts have no unindexed scan left.
The quantified order facts for a condition serve only `simp`
(`scan_for_search`). `universal_instantiation_ignores_universals_of_other_shapes`
covers the scaling.

**Compositions.** `resource_compositions` is a `ScanSet`, the same named
scans over a persistent set, and its scans are now charged: a persistent
set's own iterator records no work, so before this the store path walked
every stated composition invisibly. The composition separations that find
owned members in the two sides' blocks read the compositions
`CompositionMemberIndex` lists under those blocks: pointer separation,
shallow and through the fact graph, shallow range separation, and range
against pointer when deciding which memory facts survive a store
(`shallow_owned_separation_ignores_unrelated_compositions`, and
`heap_object_stores_and_releases_cost_the_same_at_every_position`, which
charging made fail on the old scans). Still `scan_unindexed`, each over
every composition:

- the composite frame frontier (`frame_frontier_compositions`), now over
  the compositions owning a composite only (`composite_owning_compositions`,
  read from each composition's own count; a composition without one
  expands to nothing). Its gate once walked
  every fact of every composition on each store's cell drop
  (`frame_frontier_ignores_compositions_without_composites`);
- `store_compositions` when the writer stated no store owners: the
  owned store footprint collects the member of every composition holding
  the cell, so its output is as large as the compositions that restate
  it.

**Fixed:** the composition range cover in `proves_resource_separate_inner`
while the path states a containment fact with a non-memory parent, as
composite expansion does for every opened composite. The owners of the
other range are now found by walking containment facts upward from its
blocks: facts with a memory child filed by the child's block
(`memory_containers`), then those with a non-memory child
(`resource_containers`). A memory container adds its blocks and their
address-equal blocks; a non-memory container adds its narrowest member key
(`OwnedMemberKey::exact`). The cover reads the compositions listed under
those blocks and keys, and the work is the containment facts on the way
(`composition_cover_with_a_token_container_ignores_unrelated_compositions`;
debug builds compare every answer with the scan). The counter that chose
the scan, `nonmemory_parent_containments`, is gone.

**Fixed:** owned separation of a non-memory side. The member index also
lists a composition under the `OwnedMemberKey`s of each owned non-memory
member it adds beyond its predecessor. One key is the bucket the
composition's own direct match reads, which `direct_match_candidate_positions`
now takes from the same key. A token or composite is also listed under its
shape and first-pointer root (`ShapeRoot`). A side whose first argument is a
pointer reads only the roots `direct_match_candidates_for` reads, so
compositions owning the same composite at unrelated pointers are not
visited. The difference walks cover the owned non-memory facts beside the
memory ones (`changed_owned_inputs_from`, `owned_non_memory_input_facts`).
A predecessor from another origin is chosen by the count of both
(`listed_size`), so admission still costs what changed.
`proves_owned_resources_separate` reads the compositions listed under the
two sides' keys (`token_ownership_ignores_unrelated_compositions`,
`composite_ownership_ignores_compositions_of_other_roots`; debug builds
compare every answer with the scan).

**Fixed:** owned range separation through related roots
(`composition_separates_owned_ranges`). Each side is asked of a
composition's members under its base's related roots, in those roots'
blocks, and owned members of a valid composition are disjoint, so the
compositions listed under those blocks reach one holding both
(`owned_range_separation_ignores_unrelated_compositions`; debug builds
compare every answer with the scan).

**Accessors.** The callers of `pure_facts`, `condition_fact_pairs` and
`proposition_facts` read a whole context to copy or describe it, not to
answer a query: diagnostics after a failure, the planner's retained
premises, a rule's own prerequisites, and one copy per function, path end
or loop exit (`loops.rs` turns a loop exit's context into its path's fact
list, linear in the context per exit). One was quadratic: reused contract
paths dropped their entry premises with `Vec::contains`; they read a set.

**Derived sets.** The universal, ground, disjunction and separation sets
are `ScanSet`s too:

- the planner's premise search (`atomic_general_facts`) and case search
  (`disjunction_fact_propositions`) are `scan_for_search`; the path-fact
  walk that only asked whether a disjunction is held asks
  `has_disjunction_facts`;
- the shallow separation checks, a range against an access
  (`ranges_directly_disjoint_from_access`) or a pointer
  (`range_proven_disjoint_from_pointer`), and the directed pass of range
  separation, read `memory_separations_near`: the memory separations filed
  under the blocks their sides name, plus those with a wide side, whose
  cover can cross a base equality. A shallow containment of a narrow range
  needs the side in the range's own block, and a direct one a block of the
  pointer's affine class (`pointer_class_blocks`), so the candidates hold
  every fact the scan could use, visited in the scan's order
  (`pointer_separation_ignores_unrelated_separations`).

Still `scan_unindexed`:

- range separation with both sides matched by memory resolution
  (`memory_ranges_proven_disjoint_by_explicit_separation_for_memory_resolution`),
  which `range_proven_disjoint_from_pointer` falls through to on a miss.
  Resolution equates loaded pointers whose cells agree across snapshots,
  so this is the same open question as the memory-resolution condition
  match above.

**Fixed, by narrowing:** certifying an existential obligation
(`certification_proves_exists_obligation_from_facts`) tries only the
assumed existentials alpha-equal to it, read from the identity bucket.
Across the gate and the unit tests those were every hit (four, each with
three facts on its path); trying every other existential of the sort as
the witness source was a search for which fact to use, and is gone. It
once tried every proposition fact
(`existential_obligation_ignores_unrelated_facts`).

**Fixed:** separation of a non-memory resource. The stated separations
with a non-memory side are filed under each such side, and containment
facts with a non-memory child under that child. Containment of a
non-memory resource is identity or a chain of containment facts down to
it, so its containers are walked upward from it and only their
separations are read (`separations_with_side_containing`). A memory parent
on the way contains by range, which no key spells, and falls back to the
scan. `token_separation_ignores_unrelated_separations` covers it.

The memory effect facts are filed under each memory they name; the
resolution check of two snapshots
(`memory_snapshots_directly_proven_equal_for_memory_resolution`) reads all
of them, because it matches memories up to the load's pointer. It belongs
to the memory-resolution question too.

### The 2026-10-20 audit

The list below comes from an audit of master on 2026-10-20. Each full iteration of
a fact collection now charges one unit per element
(`src/kernel/fact_collections.rs`), so a scan is no longer invisible to
scaling tests. "Uncharged" means the
scan records no deterministic work, so today's scaling tests can't see it.

**Confirmed superlinear in one decision.** Measured on 2026-10-20 in a debug
build with a kernel probe that grows the facts related to one decision. Each
row is the work of the listed queries on a fresh `PureFactContext`, with
`v(i)` a fresh `int32` variable:

1. **Fixed:** an order chain through sums was quadratic. The order walk
   that caused it is gone (items 4 and 5): `decide` reads order only from
   the difference graph, and the bound searches in `bounds.rs` read the
   endpoint index and make at most one nested decision per bound. Work is
   now 5,718 units at 64 facts and 21,462 at 256, linear past the graph's
   32-edge limit; `decide_work_is_near_linear_in_related_facts` covers it.
2. **Fixed:** two equality classes joined by a disequality were quadratic,
   because `condition_match_candidate_keys` formed every pair of the two
   classes' spellings. `condition_match_keys_by_side` now files each key
   under its sides, and a query reads one class's keys. Work at 128 members
   fell from 450,466 to 6,946 units; `decide_work_is_near_linear_in_related_facts`
   covers it.
3. **Not a decision scan: nested `if` terms are exponential because terms
   are unshared trees.** A merged value `if c then t else t + 1` holds two
   copies of `t` (`Bitvector32Term` uses `Box`), so a depth-d term has about
   2^d nodes, and a decision is linear in that. In C the shape appears as
   path explosion in `execute`, which runs each arm of a branch to function
   exit: d sequential branches give 2^d paths. That is accepted for a smart
   tactic, because the explicit form is linear: one `branch ensuring` per
   branch joins its arms (`mdtests/sequential_branches_join_with_branch_ensuring.md`;
   48 branches verify in 2.3 s in a debug build after expansion to simple
   tactics), and a proof `if <condition> ensuring` joins a `?:` the same way
   (`mdtests/sequential_conditional_expressions_join_with_a_proof_if.md`).
   `execute` now stops past 1,024 splits and names those joins,
   instead of running about 6 s (release) to its step budget.

A plain chain `v(i) < v(i+1)` to a constant, and equality classes of sums,
are linear in the same probe. Each of these three becomes a scaling test in
`src/scaling_tests/` when it is fixed: work at the larger size at most about
four times the work at a quarter of it.

**Condition decision and order reasoning:**

4. **Fixed by removal:** `has_order_path`, the order walk inside `decide`,
   collected and filed every order fact once per fact set, uncharged. Across
   the gate it proved 12 orders the difference graph did not, and removing it
   changed no verdict outside its own tests. `decide` now reads order from
   the difference graph, which is updated per fact and follows at most
   `EDGE_LIMIT` (32) edges per query: an order chain longer than that is left
   undecided, and a proof states an intermediate bound. The bound searches
   in `bounds.rs` (`has_lower_bound_*`, `has_upper_bound_*`, and their
   `add_const` forms), which scanned every condition fact and recursed into
   `decide` along a chain, now read `signed_order_bounds`. The outermost
   search judges each bound with one nested decision; a search inside that
   decision uses constants, exact facts, and the difference graph only.
5. **Fixed by removal:** the memory-resolution order walk
   (`order_walk_index`) is gone too; memory resolution asks the difference
   graph. The graph proved 163 of the walk's 164 orders across the gate. The
   one it does not, an order between loads of one cell at two snapshots that
   differ by an unrelated store, is pinned undecided by
   `order_check_does_not_resolve_loads_across_an_unrelated_local_store`;
   recording the equality of the two loads when execution resolves one would
   let the graph prove it.
6. **Fixed:** `has_exact_strict_upper_bound` reads only the facts with its
   term as a side (`condition_facts_with_side`, an index lookup).
7. **Fixed:** the increment-overflow decisions' direct bound searches
   (`overflow_intervals.rs`) read only the facts with the operand as a side.
8. **Fixed:** the `signed_interval` fallback (`overflow_intervals.rs`) read
   every condition fact and matched endpoints by snapshot equivalence and
   memory-load resolution. It now reads the bounds `signed_order_bounds`
   files under the term, its canonical form, and the value its load
   resolves to. A fact written about another load that resolves to the term
   is no longer read; no gate verdict changed.
9. **Fixed:** `range_facts_force_equal` reads only the facts about its
   variable. `signed_constant_known_equal` (`decision.rs`) read every
   condition fact and matched sides by memory-resolution equality; it now
   reads the equality graph's constant for an atom's class
   (`EqualityGraph::known_atom_constant`, which interns nothing) and the
   `term == c` facts filed under the term. No gate verdict changed;
   `fold_nonnull_fact_uses_an_exact_composite_pointer_alias` and
   `opaque_repeated_symbolic_births_…` check it.
10. **Fixed:** `pointers_distinct_by_owned_anchors` (`decision.rs`) read
    every stated resource composition, one per call, fold and store, for
    one owning each side as a distinct member. Across the gate it ran 2,196
    times over up to 23 compositions and separated 41 pairs. It now reads
    the compositions `composition_members` lists under the two sides'
    probe bases and blocks, which reach every composition holding both
    members. No gate verdict changed;
    `owned_anchor_distinctness_ignores_unrelated_compositions` covers it.
    `offsets_distinct_by_separation`, asked of two anchored offsets whose
    blocks it does not know, read every composition too (3,514 calls over
    up to 23, 477 hits). The index now also lists a composition under its
    owned members' anchor offsets, and the check reads the compositions
    listed under the two anchors;
    `offset_distinctness_ignores_unrelated_compositions` covers it.
11. **Fixed in part:** `has_condition_fact`'s fallback, run when no key
    the query spells holds a match, read every fact of the query's kind with
    a non-atom side. It now reads the facts filed under the query's
    variables and their recorded-equality classes. Across the gate that
    finds 21 of the fallback's 33 matches; the other 12 (a ground
    `is_cons(Nil)` fact matched through a known constructor, and a load
    variable equal to another only by memory resolution) changed no
    verdict. This was most of `rbtree_erase_color_flips_red_all.click`'s
    `unfold(nleft)` cost. Of the condition helpers that call
    `condition_facts.iter().any`, the `x + 1 < y` check (`order_paths.rs`)
    and `has_anchored_bitvector_equality_fact_for_memory_resolution`
    (`condition_reasoning/simp.rs`) read only the facts with their terms as
    a side. The `bounds.rs` add-constant bound helpers read the endpoint
    index (`signed_order_bounds`). Snapshot equality (`memory_conditions.rs`)
    matches memories up to a load's pointer, so it cannot key by memory: 19
    of its 41 gate hits name neither memory exactly. It reads the effect
    facts (`memory_effect_facts`, each once) instead of every proposition
    fact; across the gate it ran 995 times over at most 8 effect facts. The
    scans in `condition_reasoning/simp.rs` (additive
    cancellation, the simp condition match and its memory-resolution scan,
    the `x + 1` simp rule, transport equality) are slow part: only the `simp`
    tactic reaches them, through `decide_condition_for_simp`, and a kernel
    check runs them only over a step's own premises (an `instantiate`
    step's listed premises, or the premises a simp certificate retains).
12. Quantified facts: `condition_reasoning/simp.rs:633` clones all order
    facts; `collect_quantified_order_facts_for_condition`
    (`proposition_reasoning.rs:2608`, `2674`) and the alpha matching at
    `475`, `584`, and `689` scan all `prop_facts`. Index:
    `atomic_quantified_facts` or an alpha key in the stated-proposition
    index. Possibly better expandable: instantiating a universal is a search
    for an instance. **Fixed in part:** selecting a universal to instantiate
    for a goal (`select_forall_int32_instantiation_evidence`) read every
    proposition fact; it reads `atomic_quantified_facts`, the set of
    universal facts, so unrelated facts of other kinds cost nothing. So do
    the alpha match for a universal goal, the quantified order facts for a
    condition, and `instantiated_universal_consequents`. **Fixed:** the fast
    sites now read universals by conclusion shape ("Every scan is named").
13. **Fixed:** the inconsistency check labelled every fact. The context
    now files each fact under its contradiction keys as it is assumed
    (`contradictions.rs`), and the check reads whether any key conflicts.
    The rules that equated order endpoints by a theory (memory resolution,
    including resolved-load endpoint keys, the add rule, conditionals,
    folds), the rule refuting an alias guard by a separation, and the rule
    refuting a pointer disequality by the congruence closure are gone;
    across the gate they found contradictions only in unit tests written
    for them.
14. **Measured, left as is:** withdrawing a fact clears the difference
    graph (`difference_graph.rs`), and withdrawing an equality clears the
    contradiction index (`contradictions.rs`); the next query rebuilds each
    from all condition facts. Both rebuild lazily, so a withdrawal costs
    nothing until a later query on the same context. Across the gate the
    graph was cleared 757 times and rebuilt 11 times over at most 11
    facts (63 in all), and the contradiction index cleared 209 times and
    rebuilt 5 times over at most 10 (35 in all). An index that drops one
    edge would cost more than it saves until a proof shows a query after
    each of many withdrawals.

**Fact-store maintenance:**

15. **Fixed in part:** the loadability index (`memory_loadable_facts`) and
    the block-pair separation index (`memory_separation_facts`) are
    persistent maps, so a fork that files one fact copies only the path to
    its own block or block pair instead of the whole index. The residual
    separation list (`nonmemory_separation_facts`, `assumptions.rs`) is
    still a copied `Vec`, and every query scans it. **Measured, left as
    is:** no fact in the gate's mdtests and examples is a separation with a
    non-memory side, so the list is never filled; its three readers ran
    12, 1,309 and 2,404 times over an empty list. Its matches go through
    containment in a composite body, which has no key to index by;
    revisit it when a proof states such separations in number.
16. **Fixed:** the memory-load condition index
    (`memory_load_condition_facts`) was reset on every condition insertion
    and rebuilt over all condition facts at the next query. It is now a
    persistent map of persistent buckets, updated when a condition is filed
    or withdrawn. Regression:
    `filing_a_load_condition_in_a_fork_shares_every_other_load`.
17. **Fixed:** the loadability shape index (`memory_loadable_shape_facts`)
    was reset on every loadability fact and rebuilt over all of them at the
    next query. It is now persistent by block, then by base fingerprint, and
    updated with the block index. Regression:
    `filing_a_loadable_fact_in_a_fork_shares_every_other_block`.
18. `recompute_content_fingerprint` (`assumptions.rs`): walks the whole
    context on clear and restriction, mostly from smart search. **Measured,
    left as is:** across the gate it ran 33,226 times over 211,944 facts in
    all, at most 155 at once. A restriction recomputes over the facts it
    has just inserted, so its walk is the size of the context it builds;
    only a clear also walks the condition facts it keeps. The fingerprint
    is a cache key, so updating it incrementally there must be exact, and
    the measured walk does not justify that risk.

**Memory and resources:**

19. Loadability across effects: the `CMemoryLoadable` route in
    `proves_atomic_without_search` (`proposition_reasoning.rs:416`) scans all
    `prop_facts`; `c_memories_connected_by_effects`
    (`memory_provenance.rs:3999`) scans all `prop_facts`, canonicalizes every
    effect, and runs a breadth-first search with `Vec::contains`, quadratic in
    effects and uncharged. **Fixed:** `c_memories_connected_by_effects`
    walks the write effects `memory_effect_facts` files under each memory
    it reaches, with a hash set of the memories seen. Across the gate it
    ran 14 times over at most 6 facts and found no connection, and the
    indexed walk agreed every time; no gate verdict changed, and
    `effect_connection_ignores_unrelated_effect_facts` covers it (the old
    search grew from 116 to 1,316 units at 16 to 256 unrelated effects).
    **Fixed:** the `CMemoryLoadable` route's outer pass, which carries a
    loadable fact across effects, read every proposition fact; it reads the
    loadable facts filed under the base's block
    (`memory_loadable_candidates_for_base`). Across the gate it ran 435
    times over at most 5 facts and never proved a fact another route had
    not; of its 304 candidates, 2 had a base in another block that memory
    resolution might have equated, and neither matched.
    `carried_loadability_ignores_unrelated_loadable_facts` covers it (the
    old pass read 17, 65, 257 facts at 16, 64, 256 unrelated ones). Callers include `memory_reasoning.rs:724` and
    `contract_certification.rs:429`. Index: effect edges keyed by snapshot,
    and `memory_loadable_object_facts`. **Fixed:** the effect-summary route
    of checked load equality (`memory_provenance.rs`) scanned every
    proposition fact for a `CMemoryEffectSummary` linking the two snapshots;
    it reads `memory_effect_summaries`, which files each summary under both
    of its memories.
20. **Fixed:** `c_memory_load_is_directly_unchanged` (`memory_provenance.rs`)
    tried every proposition fact for an effect (`CMemoryMutatesOnly`,
    `CMemoryEffectSummary`, `CHeapAllocationFreed`) whose `before` matched
    the load's, exactly or by a direct snapshot match. Across the gate it ran
    525 times over up to 86 facts and succeeded twice, both through a
    summary whose `before` was the load's `before` itself. It now reads the
    effects filed under that memory (`memory_effect_facts`, which already
    filed summaries under both their memories and now files all three
    kinds); the `after` side still matches directly. No gate verdict
    changed; `a_direct_unchanged_check_ignores_unrelated_effect_facts`
    covers it.
21. **Fixed in part:** separation. `proves_resource_contains_inner` scanned
    every proposition fact per search node; it reads `resource_contains_facts`,
    which files each `CResourceContains` fact under its parent's base block
    (memory) or the parent itself, plus the blocks of the base's exact
    aliases. The separation-interval cover read every proposition fact; it
    reads the block-pair index for the two bases' blocks and their aliases,
    and the residual non-memory list. The other `prop_facts` scans in
    `memory_reasoning.rs` (range separation, pointer-outside-range, and
    non-memory resource separation) read `separation_facts`, every
    separation fact in `prop_facts` order, so a `find` chooses the same
    fact. They are not keyed by block pair: across the gate, 2 of 1,329
    range-separation hits came from a fact between other blocks, matched
    through memory resolution, and at most 7 separation facts were held.
    Range separation's two scans are now a lookup: the separations filed
    under the blocks related to either queried base by proven equality
    (`related_pointer_root_blocks`), the blocks memory resolution can
    reach, and those with a wide side, which still share one bucket. Debug
    builds compare every answer with the scan
    (`explicit_separation_lookup_reads_only_related_blocks`).
    Still listed: all compositions at `4280` and `4563` (index:
    `composition_members`).
22. **Left as is:** the load's unresolved-cell scan
    (`eval/memory_loads.rs`) walks the memory the distinct-cell reduction
    just left: the cells of the load's alias-candidate blocks that it could
    not prove distinct. It reads no cell that reduction did not, and stops
    at the first unresolved one.
23. Every composition: `held_range_membership` (`eval/operators.rs`) and
    `loops.rs:2897`, filtered by block per composition. **Fixed for
    `held_range_membership`:** it surveys the state's resources and the
    compositions `composition_members` lists under the pointer's block,
    not every composition the path stated. Across the gate its 4,332 calls
    over up to 9 compositions gave the same answer either way (3,208
    inside, 1,098 unknown, 14 outside, 12 undecided). A composition that
    only views the block is no longer read; fewer ranges can only weaken
    an answer, and none did. `held_range_membership_ignores_unrelated_compositions`
    covers it. **Fixed for `loops.rs`:** merging the incoming context's
    compositions into a retained loop-exit context walked every incoming
    composition whenever the two sets did not share a root. It now walks
    their difference (`PersistentSet::diff`, which skips shared subtrees),
    adding each incoming composition the exit lacks;
    `set_diff_names_each_side_and_walks_the_changed_paths` covers the
    diff.
24. `split_focused_call_outcomes` copies all facts on every caught-throw
    split (`execution_joins.rs:4215`).

**Already described in the efficiency guide as accepted:** loan havoc costs
cells times symbolic loans; direct and explicit transport contexts are
uncharged (`assume_proposition_uncharged`, `assumptions.rs:6688`;
`fact_transport.rs:521`, `529`; `transition_certification.rs:727`); certifying
early-return completion is quadratic; binding inheritance is linear in the
number of bindings. Under the fast-part rule these are scans too, and
`verification-efficiency.md` stops calling them accepted.

The memory shape the probe did not build, a load that looks back across many
stores, still needs a reproduction.

## Decisions

Decided by the maintainer on 2026-10-20.

1. **`decide` is fast checking.** Simple tactics may use it. It needs
   per-query fuel and work charging, and scaling tests on related facts.
2. **A helper that finds nothing is a search miss, not a tactic refusal.** The
   error names what was not found and the syntax that supplies it, for
   example "no available fact establishes premise `P`; write
   `apply(t(x)) using { … }`, or add `have P by …` first". This gives a
   two-way rule:
   - the elided form fails when the helper finds nothing. That is a heuristic
     miss; the fix is to supply the argument.
   - the explicit form fails only when the check refuses it. That is a real
     refusal, and the only kind that can be a `failing-tactic` bug.

   `click docs` gains a fourth refusal meaning, and the tracing skill gains
   the rule "on a search miss, write the argument".
3. **No separate budget class for helpers.** A tactic whose argument is elided
   is a smart site; the same tactic with the argument written is simple. This
   is how `apply(t(x))` and `apply(t(x)) using {…}` already work, so helper
   search runs on the smart budget, `click profile` lists a slow elided form
   as SMART (expand it), and `click expand` writes the argument. A tactic
   whose lookup usually succeeds without a helper, such as `assumption()`,
   counts as a smart site only when its helper actually ran.
4. **`execute_until` is a variant of `execute`.** It is not a fifth smart
   tactic.
5. **Missing premises.**
   - `apply` and `apply(ih)` stop running `auto` and `simp` on missing
     premises. The elided form only looks up each premise. A premise that is
     not available is a search miss telling the user to add `have P by …`
     first. `click expand` already writes auto-proved premises as `have`s
     before the `apply`, so expanding an affected proof migrates it.
   - Bare `close_invariants()` becomes sugar for per-member `simp()`. Its own
     premise selection, trimming, and `normalize` fallback move into `simp`
     and `arithmetic`, or are dropped. It does not leave open goals: Click
     has no general open-goal stack inside a loop body, and
     `close_invariants() by {…}` is already the explicit form.
6. **One closer, and the proof at one program point** (2026-10-25; phase F).
   - `simp` and `auto` become one tactic, `solve`, which closes one goal and
     never runs C. On a single goal the two already run the same search;
     they differ only in which goals a written form acts on after execution.
   - What an omitted proof means, and what follows the last written tactic
     of any script, is one implicit loop: `solve` an open goal, `step` a
     statement with one successor, split at one with several and run the
     loop on each arm, and stop at function exit with every goal closed. An
     omitted proof is the empty script.
   - The proof is at exactly one program point at a time. `execute()` is the
     only tactic that breaks this today: it leaves every exit path at once
     and applies the rest of the script to each.
   - `by solve();` stays accepted although it is redundant: it is a handy
     place holder to replace with another tactic.
   - Refined the same day. The only slow parts of a proof are `solve` and
     the searches behind elided arguments, and both expand to simple
     tactics. Out as written tactics: `simp`, `auto`, `execute`,
     `execute_until` and `arithmetic`. In: `solve`, with an optional `using`
     list, and `step_until` beside `step` and `branch` to advance.
     `arithmetic_certificate { … }` stays as the explicit form `solve`
     expands an arithmetic step to. No written tactic forks, so a script is never
     copied onto several paths: the only split a script sees is one it
     writes (`branch`, `if`, `cases`, `match`) or the implicit tail's.

## Plan

The principle describes an end state. The work below reaches it in small
PRs, each green on its own and each worth having even if later steps wait.
It runs in four phases: cleanups and guard rails that change no verdicts,
then consolidating the engines, then one tactic at a time, then tooling and
documentation. A step marked *verdicts* can change verdicts; a proof it breaks
is migrated with `click expand` in the same PR, and the PR explains each
verdict change.

### Phase A: cleanups and guard rails (no verdict changes)

1. **Bound `decide`.** Done: each outermost decision runs under a fixed
   per-query fuel (`with_decision_fuel`, `DECISION_FUEL_LIMIT`). Charged
   work and every order edge a walk tests spend it, and a decision that
   spends it ends undecided without failing any budget. Tests grow related
   facts (a chain, a cycle, two large equality classes) and check work stays
   linear; a fuel-stop test checks the stopped answer is not memoized.
   `decided_without_search` is now `holds_by_lookup_or_decision`, and the
   efficiency guide's section on condition decisions describes the fuel.
   Stores between two loads are not covered yet: the fuel bounds memory
   resolution only where it charges work or checks a deadline, and no
   scaling test grows the stores.
2. **Fix the small defects.** Done: `transport` is spelled correctly in
   certificate refusals, `SimpleTactic::CloseInvariants` is gone, and the
   explicit induction step is named `ProofStep::ApplyInductionUsing`.
3. **One source for classification.** Done: see the classification bullet
   under "Current state".
4. **Correct the contradictions that are wrong about today's behavior.**
   Done: the implicit claim closer, `auto`'s order, and bare `apply` are
   described as they behave, and `docs/concepts/smart-and-simple-tactics.md`
   states the target principle, marked as the target.

### Phase B: consolidate the engines

5. **One arithmetic entry point, with no change in behavior.** Done:
   `src/surface/checking/arithmetic_engine.rs` owns the special, `Integer`
   affine, and signed planners, which are now private to `surface::checking`,
   so no other module can call one directly. `arithmetic()` and post-execution
   `arithmetic using` take its ordered `arithmetic_plans`. `simp`, `simp
   using`, `close_invariants`, and the certificate transcriptions call one
   engine at a time through `plan_arithmetic`, because `simp` interleaves the
   engines with its other strategies; step 7 settles that order.
6. **Simplex behind the arithmetic entry point.** Done: simplex refutation
   is `arithmetic`'s last engine (`ArithmeticEngine::IntegerRefutation`), so
   `arithmetic() using` proves an `Integer` bound from any number of listed
   premises, and `simp`'s `Integer` attempt over its selected premises tries
   it after the affine planner. The bridged and equality-by-bounds closures
   select their premises and then close with `arithmetic() using`; the
   machine-goal and definedness closures had no planner of their own, only
   nested `auto` and the solver. The solver, now `simp`'s selected-premise
   arithmetic (`selected_arithmetic`), still plans through
   `refute_integer_goal` itself, because it adds the type
   ranges of the observations it selects. One mdtest changed verdict:
   `arithmetic() using { x < 0; x >= 0; }` now proves its goal, since the
   premises contradict each other.
7. **Move `auto`'s rewrite search into `simp`.** Done in part: the single
   connected-equality rewrite and the depth-3 chain are `simp`'s last
   strategy (`try_connected_rewrite_closure`), tried also when the facts
   decide the goal false, and `auto` no longer runs them itself; a nested
   `simp` inside the chain does not start another. No gate verdict changed.
   Of `simp`'s own equality-rewrite searches, the early goal-local probe in
   its atomic step is gone: the full indexed search tries the same probe
   later, and switching it off changed no gate verdict. The other searches
   stay because the connected chain does not cover them. Switched off one
   at a time, the selected-premise chain proves a step of
   `examples/arena`, and the indexed goal-local search proves a step of
   `examples/modeled-binary-tree` and
   `mdtests/c_named_function_contract_refines_vacuous_guarded_clause.md`.
   The restricted chain is `simp() using`'s, which reads no ambient fact.
   Switched off together, they also cost the `authority_symbolic` mdtests
   and `examples/bounded-pool`, so they overlap. *Verdicts.*

   Done in part, 2026-10-25: the selected-premise chain and `simp() using`'s
   restricted chain were one greedy loop over a premise list. Both now run
   the connected chain's search (`rewrite_search`), with the listed
   equalities as its candidates and each used at most once
   (`try_premise_equality_chain_closure`). `RewriteClosers` says what may
   close a rewritten goal: `Selected` keeps the old chain's direct, typed
   atomic and `normalize` closers, with no nested `simp`, which would
   select the same premises again; `Listed` reads only the `using` list.
   The greedy loop is gone, and no gate verdict changed. Switched off on
   the day before, the selected chain alone cost a step of
   `examples/arena`, and the restricted chain `examples/input-cursor` and
   15 mdtests. The indexed goal-local search is still separate: switched
   off alone, it costs a step of `examples/modeled-binary-tree` and
   `mdtests/loop_old_parameter_resource_argument.md`.
8. **Move definition-condition reading and constructor join into `simp`.**
   Done: both are part of `simp`'s last strategy over the connected facts
   (`try_connected_fact_closure`), definition reading first and constructor
   join after the rewrite chain, and `auto` no longer runs them itself. No
   gate verdict changed (`mdtests/simp_reads_definitions_and_constructor_equations.md`).
9. **One fixed order inside `auto`:** execute, then `simp`, then bounded case
   splits, for both a stated `have` and after execution. Done: `auto` is
   `execute()` and then `simp`, on a stated fact and after execution alike.
   What `auto` called the solver is `simp`'s arithmetic from premises it
   selects (`src/surface/proof/selected_arithmetic.rs`): `simp` runs it on an
   arithmetic goal after its cheap indexed derivations and goal-equality
   rewrite and before its unfold and transport strategies, and runs the
   64-bit and native `Integer` readings last. `simp` already splits
   conjunctions, implications and disjunction cases itself, so `auto`'s own
   conjunction and implication closures are gone. A loop bundle member's
   named-premise closure selects nothing, and neither does a `simp` nested
   in the connected-fact search, which runs once arithmetic has missed. The
   arithmetic's own subgoals, such as an equality's two bounds or an
   operand's definedness, are proved by the same arithmetic and then by
   `simp` with no arithmetic of its own, so a subgoal opens no subgoals. Two verdicts changed, both to proofs: `simp()` now proves the
   scaled chain in `mdtests/have_by_simp_chains_a_scaled_bound.md`, and a
   Rust panic check under `requires x <= 18446744073709551614u64 - y`
   verifies, since that bound is an exact `Integer` difference and implies
   the check. *Verdicts.*

### Phase C: one tactic at a time

10. **Search-miss diagnostics.** Add the fourth refusal meaning, the
    two-way rule, the "write the argument" message, and the tracing-skill
    rule, first for `apply` and `transport`, whose explicit forms already
    exist. Messages only. Done: a smart form beside a simple `using` form of
    the same tactic elides an argument, and `click docs` and `click verify`'s
    `refused by:` give it the search-miss meaning (`SEARCH_MISS_MEANING` in
    `src/docs.rs`). An elided `apply(theorem(args))` or `apply(ih(m))` that
    finds no fact for a requirement says "this is a search miss" and names
    the `have` that states it; a bare `transport` whose planner finds no
    frame evidence says so and names the `using` form. The tracing skill and
    `docs/concepts/tracing.md` say to write the argument on a search miss,
    which is never `failing-tactic`. No verdict changed.
11. **`apply` and `apply(ih)` drop their built-in `auto`/`simp`.** The elided
    form only looks up premises. Migrate affected proofs with `click expand`.
    *Verdicts.* Done: a premise that is not an available fact is a search
    miss whose refusal names the `have` to write, spelled as the theorem's
    `requires` with the written arguments, so it lowers to the fact looked
    up. Like its `using` form, `apply(ih(m))` finds a premise stated from the
    other side of the same order claim and cites nothing for one that
    evaluates to true. Each affected proof gained the `have`s the old `auto`
    proved, stated before the `apply`: the induction and theorem mdtests, the
    C++ stack mdtests, `examples/cpp-stack`, `examples/rust-unsigned`, and two
    files of `examples/rbtree/rbtree-model`. The induction mdtests that reject
    a premise state the true ones first, so each still fails on the premise
    it was written for. `mdtests/apply_proves_a_missing_premise_by_auto.md`
    became `apply_cites_a_premise_stated_first.md`;
    `apply_does_not_prove_a_missing_premise.md` covers the miss and
    `apply_induction_finds_a_premise_stated_from_the_other_side.md` the
    mirrored lookup.

12. **`close_invariants()` becomes sugar for per-member `simp()`.** Remove
    its private premise selection, trimming, and fallback. Shrink
    `SmartTacticKind` to the four engines and update the four classification
    stores together. *Verdicts.* Done in part: a bare `close_invariants()`
    descends the bundle's conjunctions and guard spines with `both` and
    `intro` and closes every member with `simp()`, and a member `simp()`
    misses as spelled over the back edge is stated once more at the
    iteration entry and closed by `simp()` there. The named-premise
    selection, the signed and 64-bit planners over it, the universal
    closer, and the trimmed `normalize() using` fallback are gone, and so is
    `NamedPremiseClosureScope`. Two `simp` gaps the planners had covered are
    closed: `simp` now derives an atomic goal such as `0 < i` from `i >= 0`
    and the branch condition `i != 0` in an execution proof as in a pure
    one, and an `Integer` certificate premise is supplied by its native fact
    stated from either side, `i > 0u64` for `0 < to_integer(i)`. No gate
    verdict changed except one, to a proof:
    `smart_ranking_closure_reads_an_inequality_in_scope` closes a ranking
    member from the inner loop's exit fact, which the named-premise closer
    refused. Done since steps 13 and 14 made the searches of `apply` and
    `transport` lookups: `SmartTacticKind` is the four engines, and
    `execute_until` is `Execute`. A smart site's class is a `SmartSite`:
    an engine, an `ElidedArgument` (the premises of `apply(theorem(args))`
    or `apply(ih(m))`, the frame evidence of `transport(P, Q)`), or bare
    `close_invariants()`. `ElidedArgument::written_form` names the simple
    tactic the `using` form is, and `every_public_form_has_one_class` checks
    it against that form's parsed class. A refusal still spells the site as
    written. No verdict changed.
13. **`transport`.** Add an instance argument. Restrict the bare form's
    premise planner to facts about the memory involved, using an index,
    instead of every available fact. *Verdicts* for the planner change.
    Done: across the corpus, about 324 bare `transport`s, the planner's
    search over every available fact reached its selection twice and cited
    no fact either time, so it is removed rather than indexed. A bare
    `transport` cites its source alone, or nothing when the target follows
    without it, and a frame that needs more premises is written in the
    `using` form; the miss says so. No corpus verdict changed;
    `explicit_fact_transport_can_certify_a_derived_source` now lists the
    facts deriving its source. The instance argument is not added, by
    maintainer decision (2026-10-23): `instantiate(F, v)` already writes the
    instance of a universal as its own step, whose result a `using` list
    cites.
14. **Fill the remaining syntax gaps, one PR each, and in the same PR make
    that simple form do only an indexed lookup**, leaving the elided form to
    a helper:
    - a cross-snapshot citation for `assumption` and for `using` lists. Not
      added: the candidates are the snapshot-blind bucket, the same
      proposition stated at other snapshots. Across the gate's mdtests and
      examples the bucket was reached 441 times and held at most 2 facts;
      78 lookups succeeded, 7 of them `assumption` goals, each from a single
      candidate, all by the condition bridge. There is no choice for a
      citation to name; the work is the per-candidate proof, which is
      fast checking. The `assumption` reference now states the case;
    - a source fact for `extract`. Not needed: `extract(P)` finds its source
      by the written `P` (conjunct, implication-by-consequent, and
      disjunction-projection indexes), with nothing to choose;
    - a guard citation for `fold`/`unfold`, with an indexed guard lookup that
      replaces the linear `condition_facts` scan. Done without the citation:
      the scan (`proves_condition_exact_or_snapshot`) matched a guard to a
      fact stated at another snapshot, and across the gate's mdtests and
      examples it never decided a guard the exact lookup or `decide` had
      not. It is now one exact lookup (`proves_condition_exact`), so the
      guard check is the exact lookup and `decide`, both fast checking, with
      nothing left for a citation to name;
    - a held-resource or memory-range citation for resource instances. Not
      added: `directly_supporting_fact` was called 62,823 times across the
      gate's mdtests and examples. Its indexed candidates numbered at most 2
      for a token or composite and at most 3 for a memory range. A token or
      composite never had two matches. A memory range had two in 152 calls,
      and each time the chosen one was the required fact itself. A citation
      would name what the index already returns;
    - a carry list for `loop`. Done without the list: the automatic
      transport after a loop rule (and after a smart `execute` step) tried
      every memory fact against the frame. Across the gate's mdtests and
      examples it tried 1016 facts at 574 steps and carried 22, and no
      verdict changed with it removed. It is gone, with the transport
      candidate index it kept; a fact needed past a loop is carried by an
      invariant or written as `transport`.

### Phase D: tooling and documentation

15. **Tracing.** A `chosen:` line for each helper choice, a mark for which
    smart tactic a step expanded from, and the candidates a failed helper
    tried. Done: a trace step checked under a smart tactic or an elided form
    ends ``(from `execute`)`` and the like, and a step whose `using` list a
    search chose prints it written out as `chosen: apply(t(x)) using { … };`.
    A written tactic pushes its name on a trace-only stack beside its
    profiling timer, so the mark costs nothing without a trace. Since phase
    C a helper only looks facts up, so a failed helper's candidates are the
    requirements it looked up; its search miss (step 10) already names the
    one it did not find and the `have` that supplies it.
16. **Profiling and CLI reference.** Update `click profile`'s advice text, the
    expand/profile/audit/docs/verify reference pages, and
    `docs/internals/testing.md` to the final taxonomy. Done: an elided form
    was already profiled as SMART (decision 3). The profile advice, the
    profile and expand pages, and the testing guide now say what a smart site
    is, that a search miss is fixed by writing its argument, and what
    expansion writes for each kind of site. The audit, docs and verify pages
    already agreed.
17. **Final documentation pass.** One canonical definition, the tactic
    reference tables, the glossary, and the concept pages. Remove the
    remaining contradictions. Rewrite the tracing skill and
    `docs/concepts/tracing.md`. Done: `smart-and-simple-tactics.md` states
    the four smart tactics, the elided forms and the search miss as current
    behavior rather than a target, and the tactic reference intro, the
    glossary (with a new "search miss" entry), `proof-scripts.md`,
    `proof-workflow.md` and the triage page say the same and link to it.
    `proof-workflow.md` no longer says bare `apply` proves a missing premise
    by `auto`, and the `apply` table rows say they look premises up. The
    tracing page and skill say how to use the trace's origin marks and
    `chosen:` lines when splitting a link.

### Phase E: fast-part scans

18. **One scan per PR** from "Fast-part scans", confirmed bugs first. Each PR
    reproduces the scan with a scaling test over related and unrelated input,
    then either indexes it or moves it to the slow part with explicit syntax,
    and removes its line from the list. A scan in a simple tactic that
    searches waits for its phase C step.

### Phase F: one closer, one program point

The measurements below are from master on 2026-10-25, over the gate's
mdtests and examples.

- Mapping `simp` and a written `auto();` to one single-goal closer changed
  three mdtests, each about written `auto` itself: two write `auto();` with
  C still to run, which executed the rest, and one checks that `auto();`
  closed every claim. No example changed.
- Of 5,063 function proofs, 553 end with more than one exit path, mostly
  two. 820 do work other than a closer after exit; 557 of them have one
  path, so a single program point already holds there. Of the 263 with
  several paths, 237 begin with a proof `if` that tells the paths apart
  again (`execute(); if result == tail { … } else { … }`), which a proof
  `if` before the C writes directly, each arm starting with
  `step_until(function.exit)`. A later count of the source text finds fewer:
  93 written `execute();` followed in their script by a proof `if`, 17 of
  them directly, and 8 of those `if`s test `result`, which does not exist
  before the C runs, so their condition is restated over the inputs; the
  migration recounts from the source. Only 26 do the same work on every path
  (`have` 13, `fold` 9, `unfold` 3, `match`, `open` and `outcomes` 2 each).
- A written script that stops with C left is refused, with "no checked
  proof driver accepts this proof script's shape … remove tactics from the
  end", where the cause is that execution has not reached exit.

19. **`solve`.** Add `solve()` and `solve() using { … }` as the single-goal
    closer, today's `simp`, and accept `simp` as its alias. `by solve();`
    is accepted wherever `by simp();` is. No verdict changes.
    Done: the tactic reference lists `solve()` and `solve() using`, with
    `simp` named as the older spelling, `click docs simp` shows `solve`, and
    `mdtests/solve_closes_one_goal.md` checks all three spellings.
20. **The implicit tail.** Every script, the empty one included, ends with
    the loop of decision 6. A script that stops with C left is finished by
    it instead of refused; an omitted proof is the empty script. This only
    accepts more proofs. Expansion writes the loop's steps, splits and
    closers, as it writes `execute`'s today. The misleading refusal above
    goes with it.
    Done: a script that ends in a statement-level tactic is followed by the
    closer an omitted proof ends with, which at a live frontier executes
    what remains and at function exit closes what is open; a script that
    ends in a split ends in its arms, each with its own closer. The tail's
    site follows the script's last tactic, so its execution and closing are
    charged to a smart budget. The implicit closer of a written script had
    been charged nowhere: `owned_split_buffer_pipeline` spent 2,247,631 units
    (15.7 s) in it under a 2,000,000-unit smart budget. Its claim is now
    written in expanded form, and its post-execution work is 47,548 units.
    `mdtests/a_script_that_stops_with_c_left_is_finished.md` covers the tail.
    Scripts that end in a split keep the uncharged closer in each arm.
21. **A written `auto();` is `solve();`.** It closes the first open goal; the
    implicit tail closes the rest and runs any C left. Migrate the three
    mdtests. `SmartTacticKind` becomes `Arithmetic`, `Solve` and `Execute`,
    with the four classification stores, profiling and trace labels.
    Done: `auto();` parses as `solve();`. `SmartTacticKind` is `Arithmetic`,
    `Solve` and `Execute`, and what an omitted proof and the implicit
    closer stand for is the smart site `SmartSite::Implicit`, still spelled
    `auto` in refusals until step 24. The three mdtests are now
    `a_written_auto_closes_one_goal.md`,
    `a_script_that_stops_after_explicit_steps_executes_the_rest.md` and
    `a_script_that_stops_after_a_call_reports_the_remaining_goal.md`.
22. **`execute_until` is `step_until`.** It is repeated `step()` and never
    forks: it refuses at an undecided branch, and each requirement it
    crosses is proved by `solve`. Rename it, keeping the old spelling as an
    alias, and give its refusals one tactic name (today the same miss is
    reported as `step()` refused by `execute_until`, or as `execute()`).
    Done in part: `step_until` is the documented spelling, `execute_until`
    its accepted alias (`click docs execute_until` shows `step_until`), and
    refusals, profiling and trace labels say `step_until`
    (`mdtests/step_until_steps_to_a_statement.md`). It also walks a loop the
    facts decide, as `execute` does, and still never splits. A miss inside
    it still reads "`step()` is missing prerequisite … refused by
    `step_until`": the step that missed, and the tactic that ran it.
23. **Remove `execute()` as a written tactic.** Its uses, from the
    2026-10-25 count of 5,079 written `execute();`:
    - followed only by closers, or by nothing (about 4,350, nearly all
      `execute(); simp();`): delete them, since the implicit tail runs the
      C, splits, and solves each goal;
    - followed by exit work on one path (about 557, such as
      `execute(); fold(…); apply(…);`): `step_until(function.exit)` and
      the same work. `step_until` first learns to target function exit; it
      never forks, so it is refused where the C would split;
    - followed by exit work on several paths (263): each path-selecting
      proof `if` becomes a `branch` at the C `if`, or moves before the C,
      and each arm steps to exit with `step_until(function.exit)`; the 26
      that repeat work repeat it in each arm. (An earlier note here said
      `branch` serves only where the arms rejoin; that was a defect, fixed
      in step 25: an arm refused `step_until` of any target,
      `mdtests/step_until_runs_inside_a_branch_arm.md`.)

    Done in part: `step_until(function.exit)` steps to function exit and
    never splits; at a branch the facts do not decide it is refused, naming
    the proof `if` or `branch` to write there
    (`mdtests/step_until_steps_to_function_exit.md`).
    The first migration also landed: a written `execute();` followed only by
    closers at the end of a `by { … }` block is deleted, 1,481 of
    them across the corpus and documentation, and a proof left with nothing
    is omitted. It found the tail missing in three places, now fixed: the
    arm that continues past a `branch` whose other arm returned, a script
    that ends in that `branch`, and a script that ends in a proof `if` or
    `cases` before execution
    (`mdtests/a_script_that_stops_in_the_arm_that_continues_runs_the_rest.md`).
    Left for the removal step: the files tests compare by text (importer
    output, expansion fixtures and the documentation examples paired with
    them), refusal tests that name `execute`'s message, and arms of a proof
    `if` or `branch`.
    The second migration rewrote `execute();` as `step_until(function.exit);`
    in 176 files, 221 uses, wherever the file still verified; it was tried
    file by file, since which C has one path is not in the source text. It
    left 21 files whose C splits, and the files tests compare by text or
    documentation examples quote.
    For uniform exit work on several paths, repeating the work in each arm
    reads worse than the one line it replaces, so two forms replace it
    instead. A goal `unfold` moves before the C (3 files). A `fold` of the
    resource the contract produces is a search of the implicit closer: on
    each returned path that holds its body it folds it, as the written
    `fold` did, and expansion prints that fold per path
    (`mdtests/an_omitted_proof_folds_the_resource_its_contract_produces.md`);
    39 files drop `execute(); fold(…);` for it. Folds of other resources
    stay written.
    The one-line forms followed: a function's `} by { execute(); simp(); }`
    and a claim's `ensures P by { execute(); simp(); }` become the omitted
    proof, 462 uses in 257 files. As before, only files that still verify
    change, and files Rust tests name, by path or by file name, and the
    mdtests documentation examples quote keep theirs.
    Then `execute();` and its closers at the end of a longer `by { … }`
    block, on one line with other tactics or not, were dropped the same way:
    234 uses in 182 files.

    `execute` then names only the tail's stepping and splitting. *Verdicts*
    only where a migration misses; each is explained in the PR.

    Done: no source writes `execute()`, and the parser refuses it, naming
    the implicit tail and `step_until(function.exit)`. The last uses went
    the same three ways, in about 1,400 mdtests, the examples, and the Rust
    tests' own sources: by the same rules first, then the arms and refusal
    tests by hand. In an arm of a
    proof `if` or `branch`, an `execute(); solve();` becomes
    `step_until(function.exit);`, not nothing, since the tail runs after the
    arms rejoin and loses each arm's condition. Exit work on several paths
    moved before the C, as a proof `if` on the inputs or `branch`, with
    each arm stepping to exit (`list_prepend` in the linked-list examples
    now splits on `node == 0` after `step_until(statement(1))`, where it
    split on `result == tail` after execution). Tests whose subject was a
    tactic written after a splitting `execute()` (two that shared one
    certificate across paths) are gone with that state. A test that
    expands a whole function proof now expands the omitted proof's tail:
    at the closing brace when it covers several claims, at the claim when
    there is one. Refusals that named `execute` now name the tail ("the
    implicit tail split at more than N C branches") or the step it ran
    (`step()`), and the step budget `step_until` shares with the tail reads
    "execution exhausted its 10000-step budget". The trace and profile rows
    label it `implicit tail`. The migration found one parser defect, now
    fixed: a Rust trait `impl` read the `function` of a method proof's
    `step_until(function.exit)` as a `function` definition.
24. **Spelling migration and removal.** Rewrite `simp()` as `solve()`,
    `arithmetic()` as `solve() using {}`, `arithmetic() using { … }` as
    `solve() using { … }`, and `execute_until` as `step_until` across the
    corpus and library; drop the `by auto();` and `by simp();` that only
    restate the omitted proof, and turn a written `auto();` into `solve();`
    or nothing. Then remove `simp`, `auto`, `execute`, `execute_until` and
    `arithmetic` from the parser, with a refusal that names the
    replacement. Printing, expansion and diagnostics spell `solve` and
    `step_until`.
    Done in part: written `simp()` is now `solve()` in mdtests, examples, the
    standard library and documentation examples, 4846 uses in
    2165 files. Left as `simp()`: files imported from Rust or C++,
    files Rust tests name, the fixtures that check the older spelling, and
    documentation examples that quote one of them; documentation prose,
    which names `simp` as the older spelling, changes in step 25.
    A `solve() using` miss now adds arithmetic's own reason, without its
    location and except where the goal is outside arithmetic's fragment
    (`mdtests/a_solve_using_miss_reports_arithmetic_s_reason.md`).
    Written `arithmetic()` is now `solve() using {}`, and
    `arithmetic() using { … }` is `solve() using { … }`: 547 uses in 174
    mdtests and examples, kept wherever they still verify. Left as they
    were: refusal mdtests that name arithmetic's message, files Rust tests
    name, Rust and C++ imports, the standard library, and the mdtests the
    documentation and the tactic inventory quote.
    Written `execute_until(…)` is now `step_until(…)`, 97 uses in 66 files;
    the files Rust tests name and the mdtests named for `execute_until` keep
    the older spelling.

    `simp`, `auto`, `arithmetic` and `execute_until` are removed. Every
    remaining use was rewritten, the files Rust tests read and the Rust tests'
    own sources included, and the parser now refuses each spelling, naming its
    replacement (`removed_tactic_spellings_name_their_replacement`). A
    `by auto();` and the block `by { auto(); }` were the omitted proof, so they
    are deleted. The one exception is `initialize by auto()`, which becomes
    `initialize by solve()`. The special refusals of
    `step() by auto()`, `fold(…) by auto()`, `open(…) { … } by auto()` and
    `close_invariants() by auto()` give way to the removal's refusal. The
    hash-pinned historical Rust sidecars stay unchanged, and their fixture
    adapter spells them as today's. Printing and expansion write
    `solve() using { … }` where they wrote `arithmetic() using { … }`, and an
    empty list as `solve() using {};`. Diagnostics, trace origins and profile
    rows spell a written closer `solve`, the implicit tail's closer
    `implicit tail` and the closer behind a simple tactic's requirement
    `implicit closer`. A `solve() using` miss appends arithmetic's reason
    after `; `, with arithmetic, the engine, out of backticks.

    Three behaviours change with the spellings:
    - A claim's `by auto();` gave that claim a proof of its own. Omitted, two
      or more claims share the function's grouped proof, so expanding or
      locating one of them selects that proof.
    - `solve() using` on a conjunction of loop-bundle members proves them
      all, where `arithmetic() using` proved one member.
    - The closers `solve() using` tries before arithmetic cost an unsigned
      order chain more than a signed one. The chain test no longer compares
      the two types' peaks.

    A failed `have P;` is located at its function, not at the `have`, as the
    removed `have P by auto();` was; this is
    `bugs/a-failed-default-have-points-at-the-function.md`. The `execute()`
    removal followed (step 23).

    Measured 2026-10-25, with every `arithmetic()` read as `solve() using {}`
    and every `arithmetic() using { … }` as `solve() using { … }`. At first
    `solve() using` lost 42 proofs and `examples/rust-chunks-exact`: it never
    called the arithmetic engine, so it missed even `(x & 255) <= 255` from no
    premises, simplex refutation of contradictory premises, and unsigned zero
    floors. With the listed premises sent to the arithmetic engine first, as
    `arithmetic() using` sends them, no gate verdict changed, and read that
    way every proof the gate expects verified. Trying it first, though,
    rewrote the expansions of goals the other closers already prove (equality
    chains, graph normalization) into arithmetic certificates, so `solve()
    using` now tries arithmetic last, after the closers it had, and those
    expansions stay as they were. 29 refusal mdtests still refuse but print
    the generic `solve() using` miss instead of arithmetic's specific refusal
    ("reads no facts from the context", "stays within uint64", "no combination
    of the listed premises proves it"), so before removal `solve() using`
    reports its arithmetic refusal when that attempt got furthest. One,
    `arithmetic_uint32_mask_refusal_names_no_signed_overflow`, now proves its
    goal, which is true: `x < 1u32` from `x <= 1u32` and `x != 1u32`, which
    arithmetic alone could not use; it needs a goal that does not follow.
25. **Documentation review.** Read every page that describes proof tactics and
    update it for this phase: `docs/concepts/` (smart and simple tactics,
    tracing, proof-failure triage), `docs/reference/tactics/` and `click docs`
    text, the CLI reference for `expand`, `profile` and `audit`, the language
    reference, the tracing skill, example and mdtest prose, `README.md`, and
    this roadmap. No page may still describe `simp`, `auto`, `execute` or
    `execute_until` as tactics to write, an omitted proof as `execute();
    auto();`, or a proof that holds several exit paths.
    Done in part: the concept pages, the tactic and language references,
    the CLI and internals pages, the glossary, the style guide, `README.md`
    and the tracing skill describe the omitted proof as the implicit tail,
    write `solve`, `solve() using` and `step_until`, and name the older
    spellings only as such. `solve` joins the word registry. The review
    found and fixed three code issues: `step_until` of any target was
    declined inside a `branch` arm
    (`mdtests/step_until_runs_inside_a_branch_arm.md`), and two refusals
    told a written closer at a live frontier, or an undecided Rust `match`
    or throwing call, to use `execute()` or `auto();`. Step 24 then took the
    examples whose fixtures tests compare by text, the prose of mdtests that
    tested `execute()` itself, and the trace and profile labels.

    Done: a last read found the tactic reference still describing a `match`,
    proof `if` or `cases` at function exit as deciding "each outcome path";
    one path reaches function exit now, so those sections describe that
    path and its cases. `click docs auto` listed `auto()` as a smart form;
    the implicit tail's entry is now `click docs implicit`, and `auto`,
    `execute`, `simp`, `arithmetic` and `execute_until` print their
    replacement's entry. Example READMEs that still wrote `by auto()`,
    `simp` or `simp() using`, and the tracing skill's `(from `execute`)`
    origin, describe today's forms. The review found one tooling defect, now
    fixed: the tail of a written script that stopped with C left was neither
    selectable nor audited. `click expand` selects it at the script's
    closing brace (`a_written_scripts_implicit_tail_is_an_expansion_site`).
    `click audit` finds the claims whose tail ran, from their verification,
    and expands them whole; with the implicit closer off, as that expansion
    is checked cold, the tail runs no C.

Out of scope: a default join at C branches. The implicit tail splits each
branch to exit as `execute` does today, so `n` sequential undecided `if`s
still give `2^n` paths, and `branch ensuring` stays the written join.

Phase A can start at once, and phase B does not depend on it. Phase E can
run beside any other phase. Phase F's steps go in order, except that 22
can go at any time and 25 is last. Within phase C, step 10 comes before 11–13,
because those steps need its messages. Step 14's pieces are independent of
one another. Phase D follows the steps whose behavior it documents. The
tracing work in step 15 can start once step 10 lands.

## Intended regression

- **Expansion round trip.** For each of `apply`, `apply(ih)`, `transport`,
  `close_invariants`, `assumption` across snapshots, `fold`/`unfold` with
  instance choice, and `extract`:
  - an mdtest whose smart or elided form verifies;
  - its expansion writes the found argument into the same tactic;
  - the expanded form verifies with no smart tactic and no helper search.
- **Classification.** A test that the four classification stores agree, and
  that `SmartTacticKind` has exactly the four engines.
- **Scaling.** Tests over growing *related* fact sets for the simple forms of
  the tactics that lose their search (for example the guard of a conditional
  resource body, and `assumption` across snapshots). Each must stay
  near-linear.
- **No duplicated planners.** One arithmetic entry point, and a test that no
  module outside it calls the planners directly.

## Acceptance criteria

- **Exactly four smart tactics remain,** and each is documented as one
  comprehensible engine or wrapper: `auto` wraps `execute` and `simp`, and
  `simp` wraps `arithmetic`. After phase F, three remain: `solve`, which
  wraps `arithmetic`; `execute`; and `arithmetic`. An omitted proof is the
  implicit loop over `step`, `branch` and `solve`, not a fourth tactic.
  Refined (decision 6): the only written smart tactic is `solve`, besides
  the searches behind elided arguments, and `execute` survives only inside
  the implicit tail.
- **Every search outside those four is a helper** for an elided argument of a
  simple tactic. `click expand` writes the helper's result into that tactic,
  and the written form checks with no search.
- **Simple tactics do only indexed lookups,** apart from whatever the answer
  to design question 1 accepts as checking.
- **Tracing, profiling, `click docs`, and the tracing skill** describe and
  display the same taxonomy. A helper's choice, and a helper miss, are
  visible.
- **Documentation:** one canonical definition, and none of the
  contradictions listed above.
- **No unexplained verdict changes.** Any verdict change is explained in the
  PR that makes it.
