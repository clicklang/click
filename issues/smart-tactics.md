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
A tactic such as `apply`, `transport`, `close_invariants`, `step`, or `fold`
is a simple core, possibly with elided arguments, and it leaves the goals it
cannot discharge open for a later tactic. It does not run `simp` or `auto`
itself.

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

`PureFactContext::decide` (`condition_reasoning/decision.rs:290`) is fast in
practice. Synthetic stress tests up to size 1,024 found no single call over
about 0.3 ms, except queries that look back across memory stores, which cost
about 0.2 ms per store. It is not bounded by construction, though: it has no
per-query fuel, and some of its inner walks charge no work. The efficiency
guide says "the general decision `PureFactContext::decide` stays with smart
tactics", but simple checking calls it. That has to be decided one way or the
other (see the design questions below).

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
  `docs/reference/tactics/index.md`, which `src/docs.rs` parses.
  `refusal_meaning` (`src/docs.rs:71`) has three meanings and needs a fourth
  for a helper miss.
- **Small defects found along the way:**
  - `smart_tactic_spelling` maps `FactTransport` to `"normalize"`
    (`proof_certificate.rs:1002`).
  - `SimpleTactic::CloseInvariants` is never constructed.
  - `ProofTactic::ApplyInduction` is classified as smart, but
    `ProofStep::ApplyInduction` as simple.

### Documentation

The definition of smart versus simple is repeated in about eight places:

- `docs/concepts/smart-and-simple-tactics.md`
- `docs/reference/tactics/index.md:4-15`
- `docs/reference/glossary.md:51-56,132-135,966-978`
- `docs/concepts/proof-landscape.md:14-26`
- `docs/concepts/proof-state.md:16-22`
- `docs/concepts/proof-scripts.md:65-98`
- `docs/concepts/proof-failure-triage.md:186-206,299-309`
- `docs/internals/verification-efficiency.md:265-299,1131-1192`

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

These contradictions already exist:

1. **Bare `apply`.**
   - `proof-workflow.md:164-169` says it takes exact facts only and does no
     search.
   - `tactics/index.md:2133-2136` says it proves missing premises by `auto`.
2. **`auto` has three definitions.**
   - `proof-workflow.md:90-93` says it executes, then runs smart `execute()`.
   - `tactics/index.md:122-128` says `simp`, then the solver, then rewriting.
   - `tactics/index.md:2553-2601` says the solver first for a `have`.
3. **The implicit claim closer.**
   - `proof-objects.md:413-416` says `simp`.
   - `tactics/index.md:120-128` says `auto`.
4. **`assumption`.**
   - `tactics/index.md:1221,1263` says it does no search.
   - In fact it recurses into disjunctions, uses equality closure, and matches
     across snapshots.
5. **`step` and `fold`.** At least four places say they "never search", while
   each hands off to the implicit smart `auto`.
6. **"Bare `apply(ih)` is smart"** is stated three times:
   `tactics/index.md:989`, `language/index.md:1179`, and
   `pure-functions.md:249`.

## Design questions to settle first

1. **Is the kernel's `decide` checking or search?** Either accept it as part of
   fast checking, with documented bounds, per-query fuel, scaling tests on
   *related* facts, and a rename of `decided_without_search`. Or move its
   heuristic rules into `simp`/`arithmetic` and give `step`, `fold`, and arm
   choice a way to cite the deciding facts. The first is far cheaper, and
   measurements so far support it.
2. **What happens when a helper finds nothing?** Is it a refusal of the simple
   tactic, or a new "nothing found, write the argument" outcome? This decides
   what `refusal_meaning`, the tracing skill, and `click verify`'s refusal text
   say.
3. **Budgets and profiling for helpers.** Does helper search spend the simple
   budget or a separate one? Does `click profile` gain a HELPER (expandable)
   section beside SIMPLE (engine defect)?
4. **`execute_until`.** Is it part of `execute`, or a simple tactic with an
   elided target?
5. **What `apply` and `close_invariants` leave behind.** Do they leave their
   undischarged premises and obligations as open goals, so the next tactic or
   the implicit closer proves them? Today they prove them with `auto` or
   `simp` themselves, and expansion writes those proofs as `have`s or as a `by`
   body.

## Plan

Each step is a separate PR that keeps the gate green. Steps that can change
verdicts also run the nightly corpus.

1. **Settle the design questions** and state the principle in
   `docs/concepts/smart-and-simple-tactics.md` as the one canonical
   definition. The other repetitions of the definition point to it.
2. **One arithmetic entry point,** with no change in behavior. Route `simp`,
   `simp using`, `arithmetic()`, post-execution `arithmetic using`, and
   `close_invariants` through it, replacing the four copies of the planner
   sequence. Then put simplex behind the same entry point.
3. **Move `auto`'s private reasoning into the engines, one piece at a time.**
   The solver variants and the machine-to-Integer readings go to `arithmetic`.
   Rewrite search, definition reading, and constructor join go to `simp`.
   `auto` keeps one fixed order: execute, then `simp`, with bounded case
   splits.
4. **Turn the remaining smart tactics into simple tactics with elided
   arguments:**
   - `apply` and `apply(ih)`: elided `using` premises; missing premises become
     open goals.
   - `transport`: elided `using` premises, plus an instance argument.
   - `close_invariants`: open one goal per invariant member.

   Shrink `SmartTacticKind` to the four engines, and update all four copies of
   the classification together.
5. **Fill the syntax gaps,** so that every helper result can be written as an
   argument:
   - an argument for `assumption` that cites a fact at a snapshot, or a
     transport bridge;
   - a source fact for `extract`;
   - a guard citation for `fold`/`unfold`;
   - a memory-range or held-fact citation for resource instances;
   - an instance argument for `transport`;
   - a carry list for `loop`.
6. **Take search out of simple tactics.** `assumption`, `using` lists,
   `extract`, `fold`/`unfold`, `transport using`, and `loop` do only indexed
   lookups. When the argument is elided, the matching helper supplies it, and
   expansion writes it. Fix the unindexed `condition_facts` scan.
7. **Make helpers visible in tracing and profiling:**
   - a `chosen:` line in trace steps for the helper's choice;
   - marking which smart tactic a step was expanded from;
   - a list of the candidates a failed helper tried;
   - a HELPER profile section;
   - updated budgets.
8. **Clean up the documentation:** the definitions, the class tables, the CLI
   reference, the tracing skill and doc, and the contradictions listed above.
   Fix the small defects listed above.

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
