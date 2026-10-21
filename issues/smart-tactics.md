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
- **`auto` owns engines of its own** (`proof/solver_bridges.rs`,
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
  `solver_connected_premises`, `simp`'s indexed bound selection,
  `named_arithmetic_premises`, and the transport planner.

### Simple tactics that search

| Tactic | Hidden search | Where |
|---|---|---|
| `assumption()` | On an outcome goal it scans the snapshot-blind bucket. Each candidate is checked by a memory-DAG proof that its loads are unchanged. The docs say "no cross-snapshot fact transport". | `kernel/proof/object.rs:626`, `facts.rs:1592,1823`, `memory_conditions.rs:43` |
| every `using` list | A premise is matched against facts at other snapshots by the same scan and frame proof. | `facts.rs:1808`, `object.rs:944,1269,1281` |
| `extract(P)` | Chooses the source implication or disjunction by consequent. | `facts.rs:1766,1368` |
| `fold` / `unfold`: choosing the instance | Finds a held fact that entails the requirement, through pointer roots linked by equalities and memory subranges. | `resource_algebra.rs:2842-2905` |
| `fold` / `unfold` / `observe` / `open`: the guard | Scans all `condition_facts` linearly, without an index, then falls back to the general `decide`. | `resources.rs:2330-2396`, `memory_conditions.rs:89` |
| bare `step()`, `fold`, `open` close | Open obligations go to an implicit `auto`. | `execution_statements.rs:1736,1816-1940` |
| `if` / `cases` / `match` arm choice | `decided_without_search`, which despite its name calls the general `decide`. | `proposition_search.rs:260`, `fixed_state_steps.rs:456,3184,3246` |
| `transport(P, Q) using {..}` | Chooses the instance of a universal premise by scanning facts. | `proposition_reasoning.rs:672`, `fact_transport.rs:1199-1360` |
| `loop` with a verified rule | Automatic fact transport tries every memory fact. | `tactic_laws.rs:454`, `transition_certification.rs:1017-1060` |

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
| A fact at another snapshot | `at(mark / function.entry / statement(N).entry / loop(N).entry, P)` | exists, but `assumption()` takes no argument, and frame evidence needs a separate transport |
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
  as having come from `auto`, `simp`, or `execute`.
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

These contradictions remain (step 4 fixed the descriptions of bare `apply`,
`auto`, and the implicit claim closer):

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

The list comes from an audit of master on 2026-10-20. "Uncharged" means the
scan records no deterministic work, so today's scaling tests can't see it.

**Confirmed superlinear in one decision.** Measured on 2026-10-20 in a debug
build with a kernel probe that grows the facts related to one decision. Each
row is the work of the listed queries on a fresh `PureFactContext`, with
`v(i)` a fresh `int32` variable:

1. **An order chain through sums is quadratic.** Facts
   `v(2i) + v(2i+1) < v(2i+2) + v(2i+3)` for `i < n`; queries `s0 < sn`
   (true) and `s0 < v(10000)` (undecided). Work 774, 2,550, 9,174, 35,208
   units at n = 8, 16, 32, 64 (299 ms at 64). Ending the chain in `sn < 1000`
   and asking `s0 < 1000` grows the same way. Likely cause: the order walk
   files edges by atom, and a sum node reads every order fact (item 4).
2. **Fixed:** two equality classes joined by a disequality were quadratic,
   because `condition_match_candidate_keys` formed every pair of the two
   classes' spellings. `condition_match_keys_by_side` now files each key
   under its sides, and a query reads one class's keys. Work at 128 members
   fell from 450,466 to 6,946 units; `decide_work_is_near_linear_in_related_facts`
   covers it.
3. **Not a decision scan: nested `if` terms are exponential because terms
   are unshared trees.** A merged value `if c then t else t + 1` holds two
   copies of `t` (`Bitvector32Term` uses `Box`), so a depth-d term has about
   2^d nodes, and a decision is linear in that. In C the same shape appears
   as path explosion: execution splits at each ternary and each `if`
   statement and does not join afterwards, so d of them in sequence give
   2^d paths. A function of 8 sequential `x = (a < b) ? x : x + 1;`
   statements verifies in 11.5 s (debug build); 12 exhaust `execute`'s
   budget after about 54 s, and 12 sequential `if` statements exhaust its
   10,000-step budget. This needs a design decision about joining paths and
   sharing terms, not an index.

A plain chain `v(i) < v(i+1)` to a constant, and equality classes of sums,
are linear in the same probe. Each of these three becomes a scaling test in
`src/scaling_tests/` when it is fixed: work at the larger size at most about
four times the work at a quarter of it.

**Condition decision and order reasoning:**

4. `has_order_path` (`order_paths.rs:655-672`): materializes every order
   fact (`condition_order_facts`, `bounds.rs:65-116`) and files them
   (`transport_edge_index`) once per context, uncharged. A node that is not an
   atom reads every edge (`order_paths.rs:718`, `851`). The endpoint indexes
   `signed_order_bounds` and `wide_order_edges` could serve it.
5. `order_walk_index` (`order_paths.rs:1228-1300`), the memory-resolution
   walk: rebuilds over all order and condition facts per context, and reads
   every fact at load and sum nodes (`order_paths.rs:1521`). Uncharged.
6. `has_exact_strict_upper_bound` (`order_paths.rs:649`): any over all order
   facts, on every increment range check (`assumptions.rs:8386`). Index:
   `signed_order_bounds[term]`.
7. Overflow decisions (`overflow_intervals.rs:168`, `233`, `249`): scan all
   `condition_facts` for `x ± 1` bounds on every increment. Uncharged.
8. The `signed_interval` fallback (`overflow_intervals.rs:1103`): all
   condition facts, uncharged.
9. `range_facts_force_equal` (`decision.rs:1870`, `1880`) and
   `signed_constant_known_equal` (`decision.rs:1932`, `1940`): all condition
   facts, uncharged. Index: endpoint bounds, constant classes, and the
   disequality index.
10. `pointers_distinct_by_owned_anchors` (`decision.rs:798-830`): every
    resource composition times pairs of alias components. Index:
    `composition_members`.
11. Condition helpers that call `condition_facts.iter().any`:
    `order_paths.rs:471`, `1619`; `condition_reasoning/simp.rs:219`,
    `286-288` (also `prop_facts`), `322`, `459`, `681`, `732`;
    `memory_conditions.rs:89`, `197`. Mostly uncharged. Index:
    `condition_facts_by_sides`, `condition_facts_by_variable`.
12. Quantified facts: `condition_reasoning/simp.rs:633` clones all order
    facts; `collect_quantified_order_facts_for_condition`
    (`proposition_reasoning.rs:2608`, `2674`) and the alpha matching at
    `475`, `584`, and `689` scan all `prop_facts`. Index:
    `atomic_quantified_facts` or an alpha key in the stated-proposition
    index. Possibly better expandable: instantiating a universal is a search
    for an instance.
13. The inconsistency fallback (`full_inconsistency_scan`,
    `proposition_reasoning.rs:3419`, `3500`) labels every fact;
    `consistency_extension.rs` covers only plain order additions.
14. Withdrawing a fact clears the difference graph
    (`difference_graph.rs:1351-1354`), and the next query rebuilds it from
    all condition facts (`assumptions.rs:6194`).

**Fact-store maintenance:**

15. Copy-on-write indexes that are not persistent: `Arc::make_mut` on a
    `BTreeMap` or `Vec` at `assumptions.rs:5097` (`memory_loadable_facts`),
    `5594` (`memory_separation_facts`), and `5641`
    (`nonmemory_separation_facts`). An insertion into a cloned context copies
    the whole index, uncharged. Fix: `PersistentMap`.
16. `memory_load_condition_index` (`assumptions.rs:4811`): reset on every
    condition insertion (`6547`) and rebuilt over all condition facts.
17. `memory_loadable_shape_facts` (`assumptions.rs:5472`): rebuilt lazily
    over all loadable facts.
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
    and `memory_loadable_object_facts`.
20. `c_memory_load_is_directly_unchanged` (`memory_provenance.rs:4103`): any
    over all `prop_facts`.
21. Separation: `proves_resource_contains_inner` (`memory_reasoning.rs:2808`)
    scans every proposition fact per search node; other `prop_facts` scans at
    `memory_reasoning.rs:2508`, `2524`, `3210`, `3528`; all compositions at
    `4280` and `4563`. Index: the block-pair index and
    `composition_members`.
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
documentation. A step marked *verdicts* can change verdicts and also runs the
nightly corpus and the expansion audit; a proof it breaks is migrated with
`click expand` in the same PR.

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
6. **Simplex behind the arithmetic entry point.** The behavior-neutral half
   is done: `auto`'s solver plans through `refute_integer_goal` in
   `arithmetic_engine.rs`, and the refutation planner is private to
   `surface::checking`. Still to do: the bridged, machine-goal,
   equality-by-bounds, and definedness variants call `arithmetic` instead of
   their own code, and `simp` and `arithmetic` gain simplex. *Verdicts.*
7. **Move `auto`'s rewrite search into `simp`.** The single
   connected-equality rewrite and the depth-3 chain become `simp`'s rewrite
   strategy, replacing `simp`'s own equality-rewrite search. *Verdicts.*
8. **Move definition-condition reading and constructor join into `simp`.**
   *Verdicts.*
9. **One fixed order inside `auto`:** execute, then `simp`, then bounded case
   splits, for both a stated `have` and after execution. *Verdicts.*

### Phase C: one tactic at a time

10. **Search-miss diagnostics.** Add the fourth refusal meaning, the
    two-way rule, the "write the argument" message, and the tracing-skill
    rule, first for `apply` and `transport`, whose explicit forms already
    exist. Messages only.
11. **`apply` and `apply(ih)` drop their built-in `auto`/`simp`.** The elided
    form only looks up premises. Migrate affected proofs with `click expand`.
    *Verdicts.*
12. **`close_invariants()` becomes sugar for per-member `simp()`.** Remove
    its private premise selection, trimming, and fallback. Shrink
    `SmartTacticKind` to the four engines and update the four classification
    stores together. *Verdicts.*
13. **`transport`.** Add an instance argument. Restrict the bare form's
    premise planner to facts about the memory involved, using an index,
    instead of every available fact. *Verdicts* for the planner change.
14. **Fill the remaining syntax gaps, one PR each, and in the same PR make
    that simple form do only an indexed lookup**, leaving the elided form to
    a helper:
    - a cross-snapshot citation for `assumption` and for `using` lists;
    - a source fact for `extract`;
    - a guard citation for `fold`/`unfold`, with an indexed guard lookup that
      replaces the linear `condition_facts` scan;
    - a held-resource or memory-range citation for resource instances;
    - a carry list for `loop`.

### Phase D: tooling and documentation

15. **Tracing.** A `chosen:` line for each helper choice, a mark for which
    smart tactic a step expanded from, and the candidates a failed helper
    tried.
16. **Profiling and CLI reference.** Update `click profile`'s advice text, the
    expand/profile/audit/docs/verify reference pages, and
    `docs/internals/testing.md` to the final taxonomy.
17. **Final documentation pass.** One canonical definition, the tactic
    reference tables, the glossary, and the concept pages. Remove the
    remaining contradictions. Rewrite the tracing skill and
    `docs/concepts/tracing.md`.

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
- **No unexplained verdict changes.** The gate, the nightly corpus, and the
  expansion audit pass. Any verdict change is explained.
