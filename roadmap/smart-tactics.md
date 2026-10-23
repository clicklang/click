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

`SmartTacticKind` (`src/surface.rs:4211`) has eight kinds:

- the four engines: `Simp`, `Arithmetic`, `Auto`, and `execute` as two kinds
  (`SmartExecute` and `ExecuteUntil`);
- `ApplyTheorem`, which covers both `apply(theorem(args))` and `apply(ih(m))`;
- `FactTransport`;
- `CloseInvariants`.

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

The list comes from an audit of master on 2026-10-20. Each full iteration of
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
10. `pointers_distinct_by_owned_anchors` (`decision.rs:798-830`): every
    resource composition times pairs of alias components. Index:
    `composition_members`.
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
    a side. Still scanning, because they match sides semantically (simp,
    transport, or memory-resolution equality) rather than structurally:
    `bounds.rs` (`has_add_const_lower_bound_above`,
    `has_add_const_upper_bound_below`, and the two others that still iterate
    `condition_facts`); `memory_conditions.rs` (snapshot equality). Each
    needs an index keyed by the equality its match uses, or to move into
    `simp`. The scans in `condition_reasoning/simp.rs` (additive
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
    universal facts, so unrelated facts of other kinds cost nothing. Keying
    universals by their conclusion's shape remains.
13. **Fixed:** the inconsistency check labelled every fact. The context
    now files each fact under its contradiction keys as it is assumed
    (`contradictions.rs`), and the check reads whether any key conflicts.
    The rules that equated order endpoints by a theory (memory resolution,
    including resolved-load endpoint keys, the add rule, conditionals,
    folds), the rule refuting an alias guard by a separation, and the rule
    refuting a pointer disequality by the congruence closure are gone;
    across the gate they found contradictions only in unit tests written
    for them.
14. Withdrawing a fact clears the difference graph
    (`difference_graph.rs:1351-1354`), and withdrawing an equality clears
    the contradiction index (`contradictions.rs`); the next query rebuilds
    each from all condition facts.

**Fact-store maintenance:**

15. **Fixed in part:** the loadability index (`memory_loadable_facts`) and
    the block-pair separation index (`memory_separation_facts`) are
    persistent maps, so a fork that files one fact copies only the path to
    its own block or block pair instead of the whole index. The residual
    separation list (`nonmemory_separation_facts`, `assumptions.rs`) is
    still a copied `Vec`, and every query scans it.
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
18. `recompute_content_fingerprint` (`assumptions.rs:2739`): walks the whole
    context on clear and restriction (`4956`, `5002`, `7109`, `7219`), mostly
    from smart search.

**Memory and resources:**

19. Loadability across effects: the `CMemoryLoadable` route in
    `proves_atomic_without_search` (`proposition_reasoning.rs:416`) scans all
    `prop_facts`; `c_memories_connected_by_effects`
    (`memory_provenance.rs:3999`) scans all `prop_facts`, canonicalizes every
    effect, and runs a breadth-first search with `Vec::contains`, quadratic in
    effects and uncharged. Callers include `memory_reasoning.rs:724` and
    `contract_certification.rs:429`. Index: effect edges keyed by snapshot,
    and `memory_loadable_object_facts`. **Fixed:** the effect-summary route
    of checked load equality (`memory_provenance.rs`) scanned every
    proposition fact for a `CMemoryEffectSummary` linking the two snapshots;
    it reads `memory_effect_summaries`, which files each summary under both
    of its memories.
20. `c_memory_load_is_directly_unchanged` (`memory_provenance.rs:4103`): any
    over all `prop_facts`.
21. **Fixed in part:** separation. `proves_resource_contains_inner` scanned
    every proposition fact per search node; it reads `resource_contains_facts`,
    which files each `CResourceContains` fact under its parent's base block
    (memory) or the parent itself, plus the blocks of the base's exact
    aliases. The separation-interval cover read every proposition fact; it
    reads the block-pair index for the two bases' blocks and their aliases,
    and the residual non-memory list. Still listed: the other `prop_facts`
    scans in `memory_reasoning.rs`, and all compositions at `4280` and
    `4563` (index: `composition_members`).
22. Load evaluation: the unresolved-cell scan (`eval/memory_loads.rs:1162`)
    visits every cell of the memory, charged.
23. Every composition: `held_range_membership` (`eval/operators.rs:3140`) and
    `loops.rs:2897`, filtered by block per composition.
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
   and `examples/bounded-pool`, so they overlap. Covering those with the
   connected chain is still to do. *Verdicts.*
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
    refused. `SmartTacticKind` keeps its kinds for now: a kind is a smart
    site's spelling in diagnostics, so `close_invariants()` keeps its own,
    and `apply` and `transport` stay smart sites until steps 13 and 14 make
    their searches helpers.
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

Phase A can start at once, and phase B does not depend on it. Phase E can
run beside any other phase. Within phase C, step 10 comes before 11–13,
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
  `simp` wraps `arithmetic`.
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
