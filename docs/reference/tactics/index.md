# Proof tactics

This page is the reference inventory of the tactics in Click's specification
language. A tactic is either **smart**, **simple**, or **control**:

- Smart tactics may inspect ambient facts, choose premises, split paths, or
  search for a proof. They are the tactics that `click profile` may recommend
  expanding.
- Simple tactics request one deterministic checked operation without heuristic
  planning or search. They may use indexed ambient context when that context is
  an input to the operation, as it is for `step()`. They are the leaves emitted
  by `click expand` and must be fast and output-sensitive: their work may scale
  with relevant input and produced state, but not unrelated ambient state.
- Control tactics contain, scope, split, or join proof scripts. Their descendants, not
  the container itself, determine whether an expanded proof is simple.

Each simple tactic's section states what it **accepts**, a guarantee, and what
is **outside it**, with what to write instead. A simple tactic that refuses a
case its Accepts list covers is a Click bug; one that refuses a case outside
the list is working as documented. Behavior a section describes as beyond the
list is not guaranteed. [Tracing](../../concepts/tracing.md) uses this
distinction for its `failing-tactic` outcome.

## Core tactics

A handwritten proof needs about fifteen tactic words. The tables below are
lookup indexes: each form has a class, an audience, a short purpose, and a
link to its detailed rules and checked examples.

The audience is **Core** for the forms listed here, **Specialized** for a
handwritten tactic used in a narrower situation, or **Expansion output** for
a form usually written by `click expand`. These categories describe usage
in the checked examples, mdtests, and expansion output. Every listed form
remains supported.

- `execute()`: run the function to its exit, splitting at undecided C `if`s
  and open Rust enum `match`es.
  See [Execution](#execution).
- `step()`: run one C statement, to put proof steps between statements. See
  [Execution](#execution).
- `branch { ... } else { ... }`: prove each arm of the C `if` at the
  frontier. See [Execution](#execution).
- `loop { ... }` with `close_invariants()`: prove a C loop from its
  invariants, closing them at the back edge. See [Execution](#execution) and
  [Resources and snapshots](#resources-and-snapshots).
- `simp()`: simplify the current proposition goal. Whole-function proofs
  default to implicit `auto`, which executes the function before closing its
  claims. See [Automation and search](#automation-and-search) for the
  different proof-clause forms and their defaults.
- `have P by ...`: prove an intermediate fact and add it to the context. See
  [Proposition reasoning](#proposition-reasoning).
- `apply(theorem(args))`: use a verified theorem, proving its premises. See
  [Proposition reasoning](#proposition-reasoning).
- `unfold(...)`: open one layer of a pure function, a predicate, or an owned
  resource. See [Proposition reasoning](#proposition-reasoning) and
  [Resources and snapshots](#resources-and-snapshots).
- `fold(resource)`: close an owned resource from its body. See
  [Resources and snapshots](#resources-and-snapshots).
- `if P { ... } else { ... }`: split the proof on a proposition you choose.
  See [Proposition reasoning](#proposition-reasoning).
- `match value { ... }`: split the proof on an algebraic value's
  constructors. See [Proposition reasoning](#proposition-reasoning).
- `intro()`: assume an implication's antecedent or fix a universal's
  variable. See [Proposition reasoning](#proposition-reasoning).
- `induct(n) as ih` or `induct(xs) as ih { ... }`, with `apply(ih(m))`: prove
  a pure theorem by induction. See
  [Proposition reasoning](#proposition-reasoning).
- `rewrite(P)`: rewrite the goal with an available equality. See
  [Proposition reasoning](#proposition-reasoning).
- `contradiction(P)`: close an impossible case from a fact and its negation.
  See [Proposition reasoning](#proposition-reasoning).

## Which to use

Several tactics overlap. Start with the default, and reach for another only
when the default misses or when a proof must not search.

- **Running C.** `execute()` is the default. Write `step()` lines where proof
  steps must come between statements, and `execute_until(...)` to run to one
  point. `branch` and `loop` are what `execute()` does at a C `if` or loop,
  written out to state what each arm or iteration proves.
- **Closing a proposition: `simp`, `assumption`, `normalize`, `arithmetic`,
  `extract`.** `simp()`, or letting the script end so that `auto` closes the
  goal, is the default; `auto` adds a solver and a rewrite search to `simp`.
  Write `arithmetic() using { ... }` for an integer bound or equality that
  `simp` does not find, listing the premises it follows from, and
  `simp() using { ... }` to restrict `simp` to named facts. `assumption()`
  (the goal is an available fact), `normalize()` (the goal is true by
  evaluation) and `extract(P)` (one part of a fact) do no search. They are
  what expansion writes; write them by hand only in a proof that must not
  search.
- **Equalities and states: `rewrite`, `transport`.** `rewrite(P)` is the
  default: it rewrites the goal with an equality at the current state.
  `transport(P, Q)` carries a fact stated at an earlier state to the current
  one when `step` did not carry it; its `using` form, which lists the frame
  evidence, is expansion output. `simp` tries both within its bounds.
  A full pointer-value equality also rewrites displaced copies such as `p + i`,
  retaining their selected bounds. An equality of `address(p)` and `address(q)`
  supplies numeric addresses without transferring object identity or bounds.
  A frame refusal prints both written operands and the checked propositions,
  followed by the frontier effects and a shared snapshot/value legend. The
  checked propositions may simplify to `true` or `false`; those are the
  terms the checker compared. With `--trace-proof`, a rejected written
  transport retains the preceding checked path without admitting its target. A planning
  budget failure retains that prefix too; if source and target were already
  lowered, it prints their checked identities and snapshot legend without
  running more proof checks.
- **Case splits: `if`, `cases`, `match`, `branch`.** `if P` splits on any
  proposition; `cases` uses a disjunction that is already a fact; `match`
  splits on constructors; `branch` follows a C `if`. Tactics written after a
  proof `if`, `cases` or `match` are checked once, never once per arm: the arms rejoin,
  keeping the facts every arm proved, or the split is refused. An arm that
  reaches function exit is a finished path, like each `return` of the C: the
  closer that ends the proof, the implicit `auto` or a written `auto();`,
  closes its remaining goals on that path, so a split that ends a proof
  finishes each arm on its own.

## Automation and search

`by simp();` is sugar for `by { simp(); }`, and `by auto();` is the same as
omitting the proof clause.
`by auto();` and an omitted proof clause execute the function, then close its
claims with `auto`, per claim or once for a grouped proof. Closing with
`auto` tries `simp` on each open claim, then the solver and a bounded search
for a chain of rewrites on a claim `simp` leaves open. A proof script that
ends with a claim still open closes it the same way, so a script needs no
final closer. On a stated fact, `have P by auto();`, there is no C to execute,
and `auto` is the solver, then `simp`, then the rewrite search. Before the
solver, `auto` tries a goal that restates an available fact through one
connected equality, such as `f(Node(..)) == 1` beside `f(t) == 1` and
`t == Node(..)`: one `rewrite` and `assumption`, at most 16 rewrites. Written
as a step of a script, `auto();` does what the closer an omitted one stands for
does at that point: it executes whatever C remains, including after explicit
steps at a live frontier
(`mdtests/auto_after_explicit_steps_executes_the_rest.md`), and closes every
goal still open in its block, so a closer after it has no goal and is refused
(`mdtests/auto_in_a_script_closes_every_open_goal.md`). In each arm of a proof
`if` that ends a proof, it closes that arm's goals
(`mdtests/auto_closes_each_arm_of_a_split_that_ends_a_proof.md`). A written
`simp()` invokes `simp` alone. Successful smart tactics and `auto` retain the checked
surface provenance that `click expand` can render as an explicit proof.
Source-premise selection skips synthesized candidates whose rendered
propositions do not tokenize as Click, rather than counting a route through an
unnamed kernel value as a successful expandable proof.

When `auto` (or a written `execute()`) executes a C store or read that is
refused because the place lies inside a folded resource the frontier owns,
it unfolds the one owned resource whose body holds that place and retries
the operation, one layer per refused access. It never chooses between
resources: when no owned resource's body holds the place, or more than one
does, the refusal stands. Expansion writes each opening as an explicit
`unfold(...)`. The contract's resource transition folds the resource again
at function exit. A written `step()` never opens a resource. See
[`auto_opens_a_folded_resource_to_store_through_it.md`](https://github.com/clicklang/click/blob/master/mdtests/auto_opens_a_folded_resource_to_store_through_it.md)
and
[`a_written_step_does_not_open_a_folded_resource.md`](https://github.com/clicklang/click/blob/master/mdtests/a_written_step_does_not_open_a_folded_resource.md).

A failed execution `have P by auto();` names `auto` and the written `P`,
rather than an internal search step or subgoal. Exhausted verification
budgets keep their budget diagnostic. See
[`auto_failure_names_the_written_goal.md`](https://github.com/clicklang/click/blob/master/mdtests/auto_failure_names_the_written_goal.md).

`auto` reads a goal that is one of a function's `if` conditions out of a
connected fact `f(args) == k`, with `k` an integer constant: the arguments
pick the definition's `match` arms, and when every way through its `if`s
that fails the goal's condition ends in a constant other than `k`, the fact
forces the goal, as `is_rb(Node(.., left, right)) == 1` forces
`is_rb(left) == 1`. An argument that a connected equation names as a constructor,
such as a `match` arm's `up.model == Context::Left(..)`, is replaced by it:
the fact is first restated as a `have` by rewriting with that equation. The proof is ordinary checked steps: `if` the goal
holds, `assumption`; otherwise a proof `if` on each condition met before the
goal's, and at each end `have f(args) != k` by `unfold` and
`normalize() using` the conditions taken, then `contradiction`. At most 16
connected function facts are read, each up to 16 ends; a `match` that its
arguments do not decide, or an end that is not a constant, is a miss. See
[`auto_reads_a_condition_out_of_a_definition.md`](https://github.com/clicklang/click/blob/master/mdtests/auto_reads_a_condition_out_of_a_definition.md)
and
[`auto_does_not_read_an_unforced_condition.md`](https://github.com/clicklang/click/blob/master/mdtests/auto_does_not_read_an_unforced_condition.md).
The function may be generic, and `bool`-valued with `true`/`false` ends: the
fact `list::contains(xs, x)` reads as `== true`, and is refuted by
`have not list::contains(xs, x)`. An end that applies a defined function, as
`list::contains(Nil, x)`, is followed into that definition (at most 4 deep)
and unfolded after the fact's own application. A condition spelled other than
the goal, `v == x` against a postcondition's `result == x`, matches when it
lowers to the same goal. So `list::contains(Cons(v, Nil), x)` forces `v == x`
([`auto_reads_a_condition_out_of_a_generic_bool_definition.md`](https://github.com/clicklang/click/blob/master/mdtests/auto_reads_a_condition_out_of_a_generic_bool_definition.md),
[`auto_does_not_read_an_unforced_generic_condition.md`](https://github.com/clicklang/click/blob/master/mdtests/auto_does_not_read_an_unforced_generic_condition.md)).

Signed `int32` arithmetic substitutes equalities: `x == 5` bounds `x` on
both sides, so it proves `x - 1` defined and closes `x - 1 == 4`; a listed
`a == b + 1` with `b` bounded converts to `a - b == 1` and bounds `a`, and
`c == a + 1` converts after it. A bound substitutes through such equalities
in turn to the listed bounds on what remains. `simp` gathers a goal
variable's equalities beside its bounds when the bounds alone decide
nothing, so a callee's `ensures o.size == old(o.size) + delta`, about a
resource field or a cell, supports arithmetic across calls (see
[`arithmetic_using_chains_equalities.md`](https://github.com/clicklang/click/blob/master/mdtests/arithmetic_using_chains_equalities.md)
and
[`abstract_resource_field_call_facts_support_arithmetic.md`](https://github.com/clicklang/click/blob/master/mdtests/abstract_resource_field_call_facts_support_arithmetic.md)).

For a signed `int32` bound, `simp` can use an indexed equality of a goal
operand to a literal even when that call-derived equality has no recorded
source spelling. It first proves the equality in a checked nested `have`
using the operand as written in the goal, then rewrites and closes the bound.
False bounds and equalities invalidated by a later store remain refused; see
[`post_call_constant_equality_proves_a_bound.md`](https://github.com/clicklang/click/blob/master/mdtests/post_call_constant_equality_proves_a_bound.md).

Refused call prerequisites name the callee and the original required-clause
position, including clauses already discharged. Statement-step diagnostics
use the written tactic position in the current block, counting preceding
`have` steps. See
[`call_prerequisite_names_the_second_source_clause.md`](https://github.com/clicklang/click/blob/master/mdtests/call_prerequisite_names_the_second_source_clause.md)
and its first-clause companion.

For ordinary authoring, start with the omitted default, `by auto();`, or the
smallest comprehensible smart tactic. Use `click profile` before replacing a
smart tactic with an exact explicit proof. The simple forms below are public,
maintained Surface Click, but long `using` blocks are normally expansion output
rather than a recommended first draft.

When a call's generated pointer has no source struct layout, expansion spells
an indexed array field as an explicit typed read at its byte address. This
retains the field offset and element width when reparsed; it grants no read
authority. Named struct pointers and library model accessors retain their
ordinary spelling. The Rust
assignment-operator audit checks this through an erased local array pointer.

For equality of a 32-bit or 64-bit machine integer with a literal, `simp` and
`auto` stop searching when current facts already decide the opposite truth
value. An inconsistent context remains eligible for contradiction closure.
The reference-call scaling regression compares valid results with false
literal results over four sizes; refusal does not spell every old call fact.

Smart tactics are deliberately incomplete heuristics. A prompt failure means
that this search did not find a proof within its budget, not that Click's
engine is broken. Split a broad tactic into smaller operations or write the
relevant proof steps explicitly. Improve shared search only for a general,
measured proof pattern; do not tune it around each difficult proof. In
contrast, a smart success that cannot expand into normally verifiable source, a
missed deadline, or a proposition that cannot be expressed with simple tactics
is a tooling gap.

The **Verified success** column names a positive fixture exercised by the
ordinary gate. `docs/reference/tactics/fixtures.toml` maps every selectable
variant to an exact source needle; a bidirectional test rejects a new tactic
without a fixture or a stale mapping whose source no longer contains that use.

Condition-premise search is one such heuristic: it tries individual ambient
condition facts and pairs until it finds sufficient explicit premises or reaches
the active smart-tactic deadline. It does not discard facts after an arbitrary
context prefix. A normal miss reports the summarized target and recommends
smaller execution steps or exact premises; `simp() using { ... }` constrains
pure search to named facts, while a shorter run of `step();` lines isolates
the one execution transition that fails.

## Execution

| Form | Class | Audience | Purpose | Details |
| --- | --- | --- | --- | --- |
| `mark name;` | simple | Specialized | Name the current execution state. | [Reference](#proof-marks) |
| `step()` | simple | Core | Execute one checked statement transition. | [Reference](#single-statements) |
| `let { result: name } = step()` | simple | Specialized | Bind the checked value of a scalar assignment. | [Reference](#binding-a-statement-result) |
| `execute()` | smart | Core | Execute through the function and split undecided paths. | [Reference](#execution-to-function-exit) |
| `execute_until(statement(N))` | smart | Specialized | Execute up to a selected source point. | [Reference](#execution-to-a-program-point) |
| `branch [ensuring { ... } then] { ... } else { ... }` | control | Core | Prove and join the arms of source control flow. | [Reference](#source-branches) |
| `loop [as name] { ... }` | control | Core | Prove a loop from its invariants and ranking obligations. | [Reference](#loop-transitions) |
| `step(Contract)` | simple | Specialized | Select a named contract for a call. | [Reference](#calls-through-named-contracts) |
| `step(callee(...), { binder: instance })` | simple | Specialized | Map resource instances and bind call outputs. | [Reference](#calls-with-resource-bindings) |
| `step(Contract, { handle: instance, ... })`; `step(Contract, { binder: instance })` | simple | Specialized | Select a contract and map its resource instances. | [Reference](#named-contracts-with-resource-bindings) |
| `step(...) by { ... }` | control | Expansion output | Supply an explicit proof for one open obligation. | [Reference](#one-statement-obligation) |
| `step(...) { requires P by ...; }` | control | Expansion output | Supply proofs for selected open obligations. | [Reference](#several-statement-obligations) |

The boundaries are intentional: `step` is one concrete transition, `branch`
and `loop` unpack the corresponding C control flow at the current frontier,
`loop` constructs and applies one verified abstract loop transition,
`execute_until` repeats transitions to a program point, and `execute` runs to function
exit. A branch continuation executes once after its arm states have joined.

Marks are local to one proof and their names cannot be rebound. They remember
an already-reached state; they are not source labels, execution targets, or
saved states that can be restored. In particular, `execute_until(name)` does
not target a proof mark.

Expansion of execution automation emits one `step();` line per executed
statement, followed by the outcome closers. Expansion recurses through `loop` and materializes omitted
phase proofs at the loop keyword. The older numbered-loop summary syntax
remains migration compatibility and should not be used in new proofs.

### Proof marks

**Form:** `mark name;`

**Specialized.** Write it to name the current state so a later fact can refer to
it with `at(name, ...)`. At any live execution frontier, add a proof-local name
for the current snapshot without advancing C.

**Failure, checking, and tools:**

A duplicate name fails. Enclosing marks remain visible in nested loop
preservation proofs; marks created inside a preservation proof remain local to
it. Loop invariants use `at(loop(n).entry, e)` rather than proof-local marks.
Click records the exact snapshot; expansion leaves the simple tactic unchanged,
and profiling attributes only its bounded checking work.

**Checked examples:** [`proof_mark_current_frontier.md`](https://github.com/clicklang/click/blob/master/mdtests/proof_mark_current_frontier.md)

### Single statements

**Form:** `step()`

**Core.** At a live C frontier, execute the next statement with every fact in
the proof context visible to the kernel. At a C `if`, an available condition
fact selects and enters one arm; at a loop head, it evaluates the condition once
and enters one iteration or advances past the loop.

A maybe-throwing call has two successors, like an undecided C `if`, so `step()`
refuses it and names the `outcomes` form that proves both.

**Failure, checking, and tools:**

A prerequisite the context cannot prove, or an unsupported transition, fails at
that statement with that diagnostic. A requirement the direct check cannot
establish is left open by the fast path, and the step proves each such
obligation by an implicit `auto` at its pre-state, which expansion prints as
`step() by { ... }` for one obligation or `step() { requires P by ...; }` for
several.

An `assert`'s false-path obligation (as a Rust overflow check lowers to) is
spelled as the asserted condition at the pre-state, less any disjunct an exact
fact refutes, and the proved condition prunes the false path. When `auto` cannot
spell or prove an obligation, the step is refused at it with the fast path's
diagnostic; a step never searches the proof context for an obligation.

Click carries no fact by list: a fact about a cell the context proves untouched
keeps that cell's name. Expansion leaves a step unchanged unless the implicit
`auto` proved an obligation. Profiling charges the step its one transition, and
the implicit `auto`'s work is a separate smart `implicit auto` row at the step.

**Checked examples:** [`smart_step_carries_prior_call_facts.md`](https://github.com/clicklang/click/blob/master/mdtests/smart_step_carries_prior_call_facts.md)

### Binding a statement result

**Form:** `let { result: name } = step()`

**Specialized.** Write it when a later fact must name an assigned value after
its local is overwritten or leaves scope. Execute the scalar assignment at the
current frontier and bind its checked value to an immutable proof name. The name
continues to denote that value after the source local is overwritten or leaves
scope.

**Failure, checking, and tools:**

Requires a scalar assignment and a fresh name. The ordinary step checks every
access and arithmetic prerequisite; the binding adds no assumption. Calls with
binder maps use the call-result form below. Expansion retains the binding
unchanged.

**Checked examples:** [`step_result_binding_names_checked_values_and_survives_overwrite`](https://github.com/clicklang/click/blob/master/src/surface/tests/project_tests.rs)

### Execution to function exit

**Form:** `execute()`

**Core.** From a live frontier, run to function exit on the checked proof: one
`step()` per statement, a `branch` at each undecided C `if` or call outcome, and
a proof-level case split where a condition or statement needs explicit path
selectors (a short-circuit, a symbolic `switch`, a may-alias load), and a
proof `match` at a Rust enum `match` whose variant is open, binding each
field as `<local>_<variant>_<index>` ([Rust enums](../rust.md#enums-and-match)).

A loop the context decides is walked one iteration at a time, within a
10,000-step budget.

**Failure, checking, and tools:**

The first statement that cannot run in the whole proof context fails the tactic
with that step's diagnostic, and no partial result is kept. Expansion emits the
explicit steps, splits, and branches, and profiling attributes them to the
tactic. Automatic path selectors must re-lower to the exact checked condition;
their native load widths and short-circuit operand facts are preserved.

Inside an explicit `branch` arm, `execute()` can succeed when the arm reaches
function exit, for example through a `return`. A continuing arm must stop at
its shared continuation; an unsuccessful `execute()` there names that arm
limit. Use `step()` to finish a continuing arm and `execute()` after the join.

**Checked examples:** [`execute_branch_arm_stops_at_shared_continuation.md`](https://github.com/clicklang/click/blob/master/mdtests/execute_branch_arm_stops_at_shared_continuation.md), [`tactic_execute.md`](https://github.com/clicklang/click/blob/master/mdtests/tactic_execute.md)

### Goals after execution

When execution reaches function exit, each path's open goals are the
contract's claims in the order the contract writes them: every `ensures`, and
every `owns` and `produces` clause, whose goal is that the path still holds the
instance. `views` and `consumes` clauses make no claim. A closer (`assumption`,
`normalize`, `arithmetic`, `both`, `simp`, `simp() using`) acts on the first
open goal, and a refusal names that goal; it does not look further down the
list for a claim it could close
(`mdtests/a_closer_after_execution_acts_on_the_first_open_claim.md`,
`mdtests/simp_after_execution_acts_on_the_first_open_claim.md`). `auto` is the
catch-all: it closes every goal still open.
`assumption()` closes a resource goal whose instance the path holds
(`mdtests/closers_after_execution_close_a_resource_goal_first.md`). A closer
written when every goal on the path is closed is refused
(`mdtests/a_closer_with_no_open_goal_is_refused.md`). `fold`, `apply`, `have`
and the other tactics that change the path's facts or resources act on the path
and leave the goal list alone; the implicit `auto` at the end of the script
closes the goals still open.

Some tactics leave a claim on its own proof, which later closers continue
instead of the claim. `choose`, `witness`, `let` and `intro` open the proof of
the first open proposition claim, and `rewrite` rewrites each open claim on
its own proof. Before a tactic continues such a proof, the proof takes up the
path's current state and resources, so a later `fold` or the contract's
resource transition reaches it. A `have` written after `intro` extends that
proof. A closer that does not apply to a proof that `intro` opened is read
against the goal list instead. A closer that does not apply to a proof only
`choose`, `witness` or `let` opened is an error, since closing the claim
another way would drop the witness.

A written closer that closes no goal it acts on is refused, `simp`, `simp()
using` and `auto` included; only the implicit `auto` at the end of the
script leaves an open claim to the report that names it
(`mdtests/a_written_simp_that_closes_nothing_is_refused.md`).

### Execution to a program point

**Form:** `execute_until(statement(N))`

**Specialized.** Write it to stop execution at a chosen statement, loop, or read
and do proof work there, instead of a run of `step();` lines. From a live
frontier, execute forward to the selected statement without creating a proof
interface. `execute_until(loop(N))` selects the indexed loop entry;
`execute_until(assignment(local, N))` selects the Nth static local assignment
before it executes.

`execute_until(read(N))` stops before the Nth statement containing an explicit
scalar memory read. `execute_until(back_edge())` finishes the current loop
preservation region with checked steps; invariant and ranking closure are
separate.

**Failure, checking, and tools:**

A missing, backward, unreachable, branch-hidden, or function-exit target fails.
The indexed source layout resolves loop entries. Click checks every crossed
transition; expansion prints those steps, and profiling reports the selected
site.

**Checked examples:** [`execute_until_current_frontier.md`](https://github.com/clicklang/click/blob/master/mdtests/execute_until_current_frontier.md), [`execute_until_selects_loop_entry.md`](https://github.com/clicklang/click/blob/master/mdtests/execute_until_selects_loop_entry.md), [`execute_until_assignment.md`](https://github.com/clicklang/click/blob/master/mdtests/execute_until_assignment.md), [`execute_until_read.md`](https://github.com/clicklang/click/blob/master/mdtests/execute_until_read.md), [`execute_until_back_edge.md`](https://github.com/clicklang/click/blob/master/mdtests/execute_until_back_edge.md)

### Source branches

**Form:** `branch [ensuring { ... } then] { ... } else { ... }`

A plain `branch` starts its first arm directly with `{`. With an `ensuring`
interface, `then` separates that interface from the first arm. The same rule
applies to a proof `if`; `then` is required with the interface and refused
without it.

**Core.** At a C `if` frontier, prove every feasible arm and join nonreturning
arms into one continuation. Arms that end in one state join as they are. Arms
that end in different states join keeping what both agree on: a local or cell
both arms hold with the same value, and the resources both still own; what only
one arm established is gone, and a local one arm never initialized is
uninitialized (`mdtests/a_bare_branch_joins_arms_that_end_apart.md`,
`mdtests/a_join_leaves_a_local_uninitialized_when_one_arm_does.md`).

The optional interface says more than that: it exports facts and resources both
arms establish. `owns name: resource(...);` in it exports an instance that
carries fields: each arm supplies the instance it has bound to `name`, the join
gives `name` a fresh model, and the interface's `fact` entries are what the
proof knows about it (`mdtests/branch_ensuring_named_resource.md`).

A comparison with `at(mark, ...)` freezes only that marked expression; the
current side is checked in both arms and the joined state.

**Failure, checking, and tools:**

A non-`if` frontier, overshot arm, unproved interface item, or nondeterministic
join fails. Click follows the spelled arms and interface; expansion recurses
into smart descendants, and profiling classifies those descendants. Exported
facts retain outer proof-binding names for later snapshot rewrites, and reads
through local pointers keep their declared element types.

**Checked examples:** [`frontier_branch.md`](https://github.com/clicklang/click/blob/master/mdtests/frontier_branch.md), [`branch_interface_mixes_current_read_and_mark.md`](https://github.com/clicklang/click/blob/master/mdtests/branch_interface_mixes_current_read_and_mark.md), [`branch_interface_keeps_model_pointer_names.md`](https://github.com/clicklang/click/blob/master/mdtests/branch_interface_keeps_model_pointer_names.md), [`branch_interface_loaded_wide_pointer.md`](https://github.com/clicklang/click/blob/master/mdtests/branch_interface_loaded_wide_pointer.md)

### Loop transitions

**Form:** `loop [as name] { ... }`

**Core.** At a C loop frontier, prove initialization and one arbitrary
iteration, construct the loop rule, and advance to its abstract exit. One
iteration is a path that reaches the body's end, a `continue`, a `break`, or a
function `return`: a `continue` is the back edge; a `break` closes no invariant
and joins the loop's ordinary exits; and a `return` is terminal for the function
and owes neither the invariant nor ranking bundle.

The frontier may be one a `branch` arm or a proof-level `if` arm reached, which
is how a loop guarded by a C `if` is proved; the invariants are then established
from the arm's state, with its path condition available.

**Failure, checking, and tools:**

A non-loop frontier or failed invariant, frame, or decrease obligation fails; so
does a path that stops short of all four endings, and exits that reach different
states, which are named rather than dropped. A continuing arm owes the same
bundle as a top-level loop, including the `decreases` the enclosing termination
judgment requires.

Click checks the structural rule; expansion materializes omitted phase proofs,
and profiling reports smart descendants and simple leaves.

**Checked examples:** [`count_to_n_loop_invariant.md`](https://github.com/clicklang/click/blob/master/mdtests/count_to_n_loop_invariant.md), [`a_summarized_loop_body_return_is_certified_with_its_value.md`](https://github.com/clicklang/click/blob/master/mdtests/a_summarized_loop_body_return_is_certified_with_its_value.md), [`loop_inside_a_branch_arm.md`](https://github.com/clicklang/click/blob/master/mdtests/loop_inside_a_branch_arm.md), [`loop_inside_a_proof_if_arm.md`](https://github.com/clicklang/click/blob/master/mdtests/loop_inside_a_proof_if_arm.md)

### Calls through named contracts

**Form:** `step(Contract)`

**Specialized.** Write it when a call matches several named contracts and the
proof must choose one. At a C call frontier, select an established named
contract's ownership transition and owned footprint for this call only.

**Failure, checking, and tools:**

Missing membership, unmet preconditions, or a non-call frontier fails without
fallback. Other applicable resource-independent guarantees constrain the same
result and memory. Expansion preserves the selection.

**Checked examples:** [`c_step_contract_buffered.md`](https://github.com/clicklang/click/blob/master/mdtests/c_step_contract_buffered.md)

### Calls with resource bindings

**Form:** `step(callee(...), { binder: instance })`

**Specialized.** Write it at a call whose callee declares instance binders, to
say which owned instance each binder takes. At an ordinary C call frontier, run
one call to `callee` with every instance binder its sidecar declares bound to an
instance the caller owns. `let { binder: name, ... } = step(callee(...), { ...
})` introduces the named instances its `produces` binders create; `result: name`
in the same pattern names the C value, independently of produced resources.

The single-name overload is rejected. A callee's value binder (`views str:
cstr_at(s, _);`) takes a resource term, `{ str: cstr_at(src, n) }`, or one of
the caller's own value binders, `{ str: s }`: the named instance gives the
callee's `_` arguments their values, and the call still requires the clause at
them
([`cstr_at_call_map_names_the_string_a_call_assembles.md`](https://github.com/clicklang/click/blob/master/mdtests/cstr_at_call_map_names_the_string_a_call_assembles.md)).

A value binder the map leaves out takes them from the one held instance that
agrees with its clause.

**Failure, checking, and tools:**

The frontier must call exactly that function with that many arguments. Missing,
duplicate, unknown, wrongly typed, or unowned entries fail where they are
written, as does an unintroduced `produces` binder. A result name fails when the
call's result is discarded or the name is already a C or proof-local binding.

The input map and output pattern are the only sources of bindings; nothing is
searched or inferred. Unmapped caller instances frame. Expansion reprints both
unchanged.

**Checked examples:** [`c_call_binder_transport.md`](https://github.com/clicklang/click/blob/master/mdtests/c_call_binder_transport.md), [`c_call_binder_transport_multiple_produces.md`](https://github.com/clicklang/click/blob/master/mdtests/c_call_binder_transport_multiple_produces.md), [`call_result_in_condition.md`](https://github.com/clicklang/click/blob/master/mdtests/call_result_in_condition.md)

### Named contracts with resource bindings

**Form:** `step(Contract, { handle: instance, ... })`; `step(Contract, { binder: instance })`

**Specialized.** Write it to choose a named contract and map its resource
binders in one call step. Select an established named contract for the current C
call and map its resource binders. The same `let { result: value, output:
resource }` pattern binds its C value and produced resources.

**Failure, checking, and tools:**

Requires callee membership with the actual call signature, every input binder,
and names for every produced resource. C arguments come from the current call.
Preconditions and ownership transitions use the existing call checker.

**Checked examples:** [`named_contract_call_output_bindings.md`](https://github.com/clicklang/click/blob/master/mdtests/named_contract_call_output_bindings.md)

### One statement obligation

**Form:** `step(...) by { ... }`

**Expansion output.** `click expand` writes it; by hand, write it only to give
an obligation a different proof than the implicit `auto`. Any `step` form,
including `let` and call forms, followed by the proof of the one obligation its
fast path leaves open. The fast path checks each requirement against facts that
state it exactly and local kernel decisions, with no search.

The body proves that obligation at the step's pre-state, as a `have` would, and
the step then runs with it stated. The body is one tactic call, such as
`simp();`, or a block.

**Failure, checking, and tools:**

Refused when the fast path leaves no obligation open (superfluous) or more than
one; the second refusal spells every open obligation as a `requires` entry to
copy. The default `step()` already invokes implicit `auto` for open obligations, so
`step() by auto()` is rejected; write `step()` instead. Expansion keeps the
`by` and prints the body's checked steps. The form is checked in a claim's
linear script and in a `branch` arm
([`step_by_and_requires_in_a_branch_arm.md`](https://github.com/clicklang/click/blob/master/mdtests/step_by_and_requires_in_a_branch_arm.md)).

**Checked examples:** [`step_by_proves_its_one_open_obligation.md`](https://github.com/clicklang/click/blob/master/mdtests/step_by_proves_its_one_open_obligation.md)

### Several statement obligations

**Form:** `step(...) { requires P by ...; }`

**Expansion output.** `click expand` writes it; by hand, write it only to give
several open obligations their own proofs. Any `step` form followed by one
`requires [label:] P by ...;` entry per obligation it proves. Each `P` is
written at the step's pre-state over the caller's locals and the call's
arguments, must state exactly one obligation the fast path leaves open, and is
proved there as a `have`.

Entries may appear in any order. An obligation no entry writes is checked as a
bare `step()` checks it.

**Failure, checking, and tools:**

An entry that states no open obligation, including one the fast path already
closes, or that repeats an earlier entry's obligation, fails where it is written
and lists the open obligations. Expansion keeps each entry and prints its body's
checked steps. Like the `by` form, it is checked in a `branch` arm.

**Checked examples:** [`step_requires_proves_each_open_obligation.md`](https://github.com/clicklang/click/blob/master/mdtests/step_requires_proves_each_open_obligation.md)

## Proposition reasoning

Checked equality closure also records a contradiction when one typed scalar
class contains unequal 32-bit or 64-bit constants, including classes connected
through model getters, or when one model class contains two different
constructors. Two applications of one constructor in a class have equal fields,
so `x == Full(a)` and `x == Full(b)` give `a == b` to `simp` and `assumption()`
without a stated `Full(a) == Full(b)`; see
[`constructor_injectivity_through_an_equal_value.md`](https://github.com/clicklang/click/blob/master/mdtests/constructor_injectivity_through_an_equal_value.md). Semantic fact lookup and inconsistency checking use this
indexed evidence, so `assumption()` can close a goal in that impossible context
without another search. The evidence belongs to the current branch and is
rebuilt when supporting facts are withdrawn; it does not equate reads across
changed memory snapshots. Exact fact membership remains separate. See
[`model_getter_constant_conflict.md`](https://github.com/clicklang/click/blob/master/mdtests/model_getter_constant_conflict.md).

`extract(P)` can also project an available disjunction: each source arm
must establish `P` through its direct `and`/`or` structure and equality-backed
fact lookup. It selects stated disjunctions indexed by the values or addresses
`P` names, without scanning unrelated facts, unfolding functions, or searching
for theorems. It checks every arm and keeps their assumptions local. For example,
`(A and X) or (B and Y)` supplies `A or B` without spelling `X` and `Y`.
See [`extract_disjunction_projection.md`](https://github.com/clicklang/click/blob/master/mdtests/extract_disjunction_projection.md)
and [`loop_exit_disjunction_projection.md`](https://github.com/clicklang/click/blob/master/mdtests/loop_exit_disjunction_projection.md).

A simple tactic that adds a fact (`extract`, `instantiate ... using`,
`apply ... using`, `transport ... using`, and `obtain`) also closes a
proposition goal that it adds, when it is the last written step or only
`assumption`, `simp`, or `normalize` follows it. An added order fact closes
the goal under either spelling of the same claim: `0 <= e` closes the goal
`e >= 0`, and `a < b` closes `b > a`, for machine and `Integer` operands
alike. A written theorem application also closes the mirrored goal when
its checked conclusion was already stated in the context. When other written
steps follow, the goal stays open with the added fact available, so every remaining
step is still checked.

| Form | Class | Audience | Purpose | Details |
| --- | --- | --- | --- | --- |
| `both { ... } and { ... }` | control | Expansion output | Prove both sides of a conjunction. | [Reference](#conjunctions) |
| `outcomes { returned => { ... } threw => { ... } }` | control | Specialized | Prove each returned or exceptional outcome. | [Reference](#execution-outcomes) |
| `simp()` | smart | Core | Search available facts and bounded simplification rules. | [Reference](#simplification) |
| `simp() using { P; ... }` | smart | Specialized | Restrict simplification to written premises. | [Reference](#simplification-with-selected-premises) |
| `assumption()` | simple | Expansion output | Close a goal directly from available facts. | [Reference](#available-facts) |
| `extract(P)` | simple | Expansion output | Extract a proposition from an available fact. | [Reference](#extracting-a-fact) |
| `normalize()` | simple | Expansion output | Close a goal by evaluation without context. | [Reference](#context-free-normalization) |
| `normalize() using { P; ... }` | simple | Expansion output | Check normalization against written premises. | [Reference](#normalization-with-selected-premises) |
| `arithmetic()` | smart | Specialized | Search for arithmetic evidence for a bound or equality. | [Reference](#arithmetic-search) |
| `arithmetic() using { P; ... }` | smart | Specialized | Restrict arithmetic search to written premises. | [Reference](#arithmetic-with-selected-premises) |
| `arithmetic_certificate { premise ...; conclusion N; }` / `arithmetic_certificate signed_int32 { ... }` / `arithmetic_certificate rules { ... }` | simple | Expansion output | Check explicit arithmetic evidence. | [Reference](#arithmetic-certificates) |
| `rewrite(P)` | simple | Core | Rewrite the goal using an equality. | [Reference](#rewriting) |
| `intro()` | simple | Core | Introduce a universal binder or implication premise. | [Reference](#introducing-a-binder-or-premise) |
| `intro() as name` | simple | Specialized | Choose the name introduced into the proof. | [Reference](#naming-an-introduced-binder) |
| `enumerate()` | simple | Expansion output | Close a constant-bounded universal from its instances. | [Reference](#finite-enumeration) |
| `contradiction(P)` | simple | Core | Close a goal from incompatible facts. | [Reference](#contradictions) |
| `instantiate(F, value)` | simple | Specialized | Instantiate an available universal fact. | [Reference](#universal-instantiation) |
| `instantiate(F, value) using { P; ... }` | simple | Expansion output | Instantiate using written premises. | [Reference](#instantiation-with-selected-premises) |
| `apply(theorem(args))` | smart | Core | Apply a theorem and search for its premises. | [Reference](#theorem-application) |
| `apply(theorem(args)) using { P; ... }` | simple | Expansion output | Apply a theorem using written premises. | [Reference](#theorem-application-with-selected-premises) |
| `unfold(function(args))` | simple | Core | Open one layer of a pure function. | [Reference](#unfolding-pure-functions) |
| `peel(function(args)) using { P; ... }` | simple | Specialized | Open a function using written branch evidence. | [Reference](#peeling-a-pure-function) |
| `match value [ensuring { ... }] { Type::Variant(fields) => { ... } ... }` | control | Core | Prove each constructor case of an algebraic value. | [Reference](#constructor-matches) |
| `induct(n) as ih` | simple | Core | Introduce strong induction on a nonnegative `int32` or a `uint64`. | [Reference](#scalar-induction) |
| `induct(xs) as ih { Type::Variant(fields) => { ... } ... }` | control | Core | Prove constructor cases with recursive hypotheses. | [Reference](#algebraic-induction) |
| `apply(ih(m))` | smart | Core | Apply an induction hypothesis and prove its premises. | [Reference](#induction-hypothesis-application) |
| `apply(ih(m)) using { P; ... }` | simple | Expansion output | Apply an induction hypothesis using written premises. | [Reference](#induction-hypotheses-with-selected-premises) |
| `have P by { ... }` | control | Core | Prove and retain a named or unnamed fact. | [Reference](#intermediate-facts) |
| `if P [ensuring { ... } then] { ... } else { ... }` | control | Core | Split a proof on a chosen proposition. | [Reference](#proposition-branches) |
| `cases { A => { ... } B => { ... } }` | control | Specialized | Prove a written collection of cases. | [Reference](#explicit-cases) |
| `open(resource) { ... }` | control | Specialized | Unfold a resource for a nested proof. | [Reference](#scoped-resource-opening) |
| `open(...) { ... } by { ... }` | control | Expansion output | Supply the proof that restores an opened resource. | [Reference](#scoped-resource-opening-with-restoration) |
| `witness { name: value, ... };` | simple | Specialized | Supply values for existential binders. | [Reference](#existential-witnesses) |
| `obtain (name: Type, ...) { P }` | simple | Specialized | Name witnesses from an available existential fact. | [Reference](#obtaining-witnesses) |

`sorry()` is a dev-only proof hole, not a tactic for committed proofs: it
parses only under `click verify --allow-sorry` and closes its goal without
checking it. See [Dev-only proof hole](../cli/verify.md#dev-only-proof-hole).

When `intro` must freshen a universal binder, it uses the reserved logical-witness
range. Existential choices use that same range, separate from C execution,
load and binder identities. Issued witnesses remain reserved even when their
instantiated body does not mention them, so later introductions and choices
cannot reuse a live proof binding.

`both { ... } and { ... }` proves an `A and B` goal by opening the exact `A`
and `B` child goals. Both arms inherit the parent assumptions; neither inherits
facts proved only in the other arm. This differs from `assumption()`, which
closes a conjunction from already-established facts. Empty or unfinished arms fail.
The `both` source location owns expansion and profiling of its nested proof;
expansion preserves both bodies with their checked steps.

`by simp();` is sugar for a script containing the same `simp()` operation at the
same proof state. Neither form implicitly executes a function. Write
`execute(); simp();` when both operations are intended, or use `by auto();`,
or end the script after `execute();` to close with `auto`. A
`simp()` written before execution has reached the function exit is refused
with the frontier it stands at; the end of a body is one `step()` of its own
(`mdtests/simp_before_exit_in_arm_names_the_frontier.md`).

Inside a `have` body, a tactic that already closed the goal (an `unfold`
whose refreshed goal is an available fact, a `transport` onto the goal, a
theorem whose conclusion is the goal) may be followed only by `assumption`,
`simp`, or `normalize`, which then assert the closed judgment and emit
nothing. So `unfold(f(x)); normalize();` means the same whether or not the
unfold alone closed the goal
(`mdtests/closer_after_unfold_closed_goal.md`); any other tactic after the
closure is refused by naming the tactic that closed it
(`mdtests/tactic_after_closed_goal_is_named.md`).

`induct` is available only in a pure theorem, must be the first tactic, and
names a proof-local hypothesis. The algebraic form is the enclosing control
tactic and therefore the only top-level tactic; its constructor arms contain
the proof steps. It is never inserted by `simp` or `auto`.

The algebraic hypothesis takes the theorem's complete parameter list in
declaration order. Only the inducted position is restricted: it must name a
field the current arm's pattern bound, of the datatype being inducted on.
Every other position may name any well-typed term, which is how a proof whose
recursive case changes another parameter — an accumulator, or a context frame
that grows the focused subtree — states its hypothesis. Passing only the
inducted argument remains the spelling for "every other parameter unchanged",
so `ih(tail)` and a complete list that repeats the other parameters are the
same instance. Each instance carries the theorem's `requires` clauses
substituted at the arguments given; a `using` block, or the premises the bare
form plans, must prove exactly those.
A theorem application's arguments and its `using` premises are written in
the same scope as a `have` goal at that point of the proof: the goal's own
binders first, then every proof local, including the bindings a proof
`match` arm introduced, the names a `let { ... } = unfold(...)` gave its
children, a `let { result: r } = step(...)` result, and a loop binder. The C null pointer constant
is accepted at a pointer-typed theorem parameter and lowers to that
type's null value, as it does at a pure function's pointer parameter.
`instantiate` and `extract` resolve their written propositions the same way.
See [`theorem_argument_arm_binding.md`](https://github.com/clicklang/click/blob/master/mdtests/theorem_argument_arm_binding.md),
[`theorem_argument_arm_binding_algebraic.md`](https://github.com/clicklang/click/blob/master/mdtests/theorem_argument_arm_binding_algebraic.md),
and [`theorem_argument_null_constant.md`](https://github.com/clicklang/click/blob/master/mdtests/theorem_argument_null_constant.md).

Bare `apply(ih(m))` is smart because it plans proofs of the fixed application
obligations. Its expansion ends in the deterministic simple
`apply(ih(m)) using { ... }` operation, which checks exactly the listed
nonnegative, strict-decrease, and substituted-requirement facts.

`enumerate` is how an explicit proof closes a finite case analysis over a
constant-bounded universal, such as a `sorted(p, 3)` postcondition: the
expanded proof spells one `have` per non-vacuous instance (typically closed by
`intro`, `instantiate ... using`, an explicit transport, and `assumption`),
and `enumerate()` checks exactly those instances against the goal's own
guard-derived ranges. A goal stated as a predicate call is unfolded to the
body that binds the instances, and the smart `simp` proves nearest pairs
first so a wider span can cite its neighbours. Instances are lowered lazily: a missing instance stops `enumerate` before
visiting the rest of the numeric range, and smart `simp` also stops generating
instances at its first failed proof. The finite-universal planner and its
retained certificate checker use the same lazy range order and still require
every in-range instance for success. This keeps refusal of a false frame over
a large constant range from materializing every element. Click never
instantiates by search: an in-range instance that is neither vacuous nor
spelled fails.

Proof-level `if` and `cases` answer different questions. `if P` is an
excluded-middle split: the else case assumes `not P`, so it cannot eliminate a
disjunctive fact whose right side is not the negation of its left. `cases`
requires the spelled disjunction to be an exact available fact and checks each
branch under exactly its assumed disjunct — the shape smart simplification
emits when a proof consumes a fact such as `selected == left or
selected == right`. Click never searches: a branch that needs the other
case's disjunct fails.

Intrinsic tactic class and selectable source-site kind answer different
questions. `have` is always a control container because it owns a nested goal.
Its selectable source site is an expandable-automation site for a supported
smart body, a simple-operation site for a nonempty entirely simple body, and a
control-container site otherwise. A `loop` is likewise intrinsically control;
when a phase proof is omitted, the `loop` keyword is the source site
that owns the generated automation. Profiling renders those site kinds as
SMART, SIMPLE, and CONTROL, while smart-site discovery and expansion select
only expandable-automation sites.

Explicit full-width unsigned bounds can also normalize pointer offsets.
For a native uint64 `index <= 2147483647u64`, `pointer + index` and
`pointer + (int32)index` denote the same address. `simp() using { ... }` checks
that the cited native bound is available and preserves the pointer stride.
A bound on the low word or a signed comparison cannot establish this unsigned
projection, and address equality grants no permission to access the backing
storage. Conditional normalization does not enter binder bodies.

When a smart `have` needs memory permissions merely to lower its goal, its
expanded proof retains the relevant viewability and order facts through
explicit transports, rewrites, extracts, or named theorem applications. A
context-free-looking result such as a normalized equality is not emitted as
bare `normalize()` if checking still needs those premises to interpret an
indexed load. A `simp() using` equality may be selected through a bounded chain
of exact equality facts whose intermediate load variables are kernel-internal
names for the same user-level loads. When frame evidence is needed to relate an
earlier load origin to the current one, the expanded proof first establishes the
current surface form with an explicit `transport`; simple `rewrite` checking
never searches for an equivalent equality. Expansion and audit verify the
complete rewritten surface proof through the ordinary entry point.

### Conjunctions

**Form:** `both { ... } and { ... }`

**Expansion output.** `click expand` writes it; by hand, a conjunction goal is
normally split by `simp` or `auto`; write `both` only when each side needs its
own explicit proof. Prove the exact left and right children of an `and` goal in
separate scopes.

**Failure, checking, and tools:**

A non-conjunction or unfinished arm fails. Arms inherit only the parent
assumptions. The source container owns expansion of its nested proof.

**Checked examples:** [`proof_both_and.md`](https://github.com/clicklang/click/blob/master/mdtests/proof_both_and.md)

### Execution outcomes

**Form:** `outcomes { returned => { ... } threw => { ... } }`

**Specialized.** Write it at a C++ call that may throw, when the two outcomes
need different proofs; `execute()` splits them for you. At a maybe-throwing
call, prove its two successors separately; each arm begins with the `step()`
that runs the call along its edge. Inside a `try`/`catch (int name)` the `threw`
arm follows the caught exceptional edge into the handler.

Outside any `try` the `threw` arm ends at function exit with that throw, while
the `returned` arm continues with the rest of the function and may hold the next
call's own nested `outcomes`. `execute()` splits every maybe-throwing call this
way, inside a C `if` arm as well as at top level, and expansion writes the split
it took.

**Failure, checking, and tools:**

The checked execution must establish exactly one edge of each kind. Each arm has
its own outcome goal and must close it; neither arm can use the other's facts or
state. Expansion preserves both certificates.

**Checked examples:** [`cpp_import.rs`](https://github.com/clicklang/click/blob/master/tests/cpp_import.rs), [`outcomes_routes_a_throw_that_leaves_the_function.md`](https://github.com/clicklang/click/blob/master/mdtests/outcomes_routes_a_throw_that_leaves_the_function.md)

### Simplification

**Form:** `simp()`

**Core.** On a proposition goal, search ambient pure facts and bounded rules for
a simple proof. A signed `int32` goal over variables is tried with one
arithmetic certificate from the indexed bounds reachable from those variables (a
bound `i < n` leads on to `n`'s bounds, up to eight variables), the same way in
a pure theorem, before execution, mid-function, in a `branch` arm, and at
function exit; a negated branch condition counts as a bound. Constant bounds on
the goal variables are tried before following relational bounds, so earlier
postconditions on those variables do not exhaust the arithmetic premise limit.

A loop bundle closer's members cite only the loop head and the contract instead.
Its arithmetic first tries the named premises whose variables occur in that
member's goal, then the complete named slice when other variables are needed.
A conjunction under implications or universals is first tried leaf by leaf with
direct logical steps, and a written conjunction is split before any search over
the whole goal, each conjunct trying direct steps first.

A comparison held only under a definedness guard (`defined(e) implies a == b`,
as a call postcondition over partial arithmetic lowers) whose consequent names a
goal operand is used once a nested `simp` proves the guard: the closer extracts
the consequent and rewrites the goal with an equality or closes from the new
fact.

An `int32` or `int64` definedness goal `defined(a + b)` or `defined(a - b)` is
closed by the checked `int32_defined` or `int64_defined` certificate rule,
citing the constant order and equality facts of that width indexed under each
operand; the rule, not the selection, decides whether the operands' ranges
exclude overflow.

A recursive specification function applied to a known constructor is
evaluated: `simp` unfolds it, then keeps unfolding the recursive calls the
definition exposes while their arguments select one arm, rewriting an argument
by a constructor equation (a supplied premise or a connected fact such as
`u == Tree::Node(..)`) when that exposes one, for at most eight checked steps.
An argument nothing fixes stays folded
([`simp_evaluates_a_recursive_function_over_known_constructors.md`](https://github.com/clicklang/click/blob/master/mdtests/simp_evaluates_a_recursive_function_over_known_constructors.md),
[`simp_does_not_evaluate_a_recursive_function_past_an_unknown_argument.md`](https://github.com/clicklang/click/blob/master/mdtests/simp_does_not_evaluate_a_recursive_function_past_an_unknown_argument.md)).

A disequality between an algebraic value and a constructor closes from an exact
equality fixing that value to a different constructor: the equality rewrites the
goal and normalization decides the constructors differ
([`simp_constructor_disequality_from_produced_field.md`](https://github.com/clicklang/click/blob/master/mdtests/simp_constructor_disequality_from_produced_field.md)).

An `int32` or `int64` definedness goal whose operand is a sum with a summand an
exact equality fixes to `0`, such as a count `A + n` with `A == 0`, first proves
the operand equal to the sum without it by `simp`, then the restated goal from
its bounds
([`simp_defined_count_after_a_zero_summand.md`](https://github.com/clicklang/click/blob/master/mdtests/simp_defined_count_after_a_zero_summand.md)).

When the goal also carries an operand's own definedness, such as a field read
through a resource, `simp` proves `defined(operand)` as a `have` and cites it in
the `int32_defined` step
([`simp_defined_read_through_a_produced_resource.md`](https://github.com/clicklang/click/blob/master/mdtests/simp_defined_read_through_a_produced_resource.md)).

A goal that reads one cell at two snapshots, such as `owner->cell[0] ==
owner->phase` right after a store wrote the first side from the second, is
proved by `transport` from the cell's reflexive equality at a recently recorded
point, with the frame evidence the transport selects as its `using` list
([`simp_frames_a_read_across_a_separate_store.md`](https://github.com/clicklang/click/blob/master/mdtests/simp_frames_a_read_across_a_separate_store.md)).

A goal that is one disjunct of an available disjunction whose every other
disjunct an exact fact refutes is proved by `cases` over that disjunction, the
refuted arms closing by `contradiction`
([`simp_disjunctive_syllogism.md`](https://github.com/clicklang/click/blob/master/mdtests/simp_disjunctive_syllogism.md)).

A goal that an available implication (or chain) concludes whose antecedents are
exactly available, such as a call guarantee `r == 0 implies X` inside the branch
where `r == 0`, is closed by modus ponens as a direct step through `extract`'s
indexed consequent lookup, with the goal's snapshots as written; an antecedent
that is not exactly available is not proved or searched for.

A guarded universal goal `forall k { G implies A }` closes from an available
`forall k { G implies A and B }` with the same binder and guards, selected by one
indexed lookup of the conjuncts guarded universals conclude. The proof is `intro()`
for the binder and each guard, `instantiate` at the introduced binder, and
`assumption()`, so `memset`'s `defined(..) and` value postcondition supplies
`bytes::all_equal`
([`simp_drops_a_conjunct_of_a_guarded_memset_postcondition.md`](https://github.com/clicklang/click/blob/master/mdtests/simp_drops_a_conjunct_of_a_guarded_memset_postcondition.md)).
A different guard or an unstated conjunct is not supplied
([`simp_does_not_weaken_a_guarded_universal_to_a_wider_range.md`](https://github.com/clicklang/click/blob/master/mdtests/simp_does_not_weaken_a_guarded_universal_to_a_wider_range.md),
[`simp_does_not_drop_a_conjunct_a_universal_lacks.md`](https://github.com/clicklang/click/blob/master/mdtests/simp_does_not_drop_a_conjunct_a_universal_lacks.md)).

Case splits consider only disjunctions sharing a variable with the goal, nested
at most twice. Equality rewriting chains through the goal's equalities,
including a scope's own `have`s and pointer equalities reaching the goal's loads
through their addresses; each link keeps up to four goal-changing rewrites,
continuing from the first and probing the others one link further.

It never executes C.

**Failure, checking, and tools:**

A bounded miss leaves the goal open and reports the target. Click checks the
chosen operations; expansion prints its proof steps, and profiling reports
search plus leaves.

**Checked examples:** [`simp_postconditions.md`](https://github.com/clicklang/click/blob/master/mdtests/simp_postconditions.md)

### Simplification with selected premises

**Form:** `simp() using { P; ... }`

**Specialized.** Write it when `simp` picks the wrong premises or searches too
long, to restrict it to the named facts. On a proposition goal, including a
contract claim after function exit, search using exactly the listed proposition
facts. A preceding `have` is available on each outcome where it was proved;
grouped proposition and ownership claims retain their checked resource
transition.

A listed guarded equality whose definedness guard is not listed has the guard
proved first, from the other listed facts when they suffice, and is then used as
its consequent. An `int32` or `int64` definedness goal cites the listed premises
that bound an operand by a constant in one `int32_defined` or `int64_defined`
certificate.

**Failure, checking, and tools:**

A missing fact or missing simple rule fails. Click uses the generated explicit
proof rather than repeating search; expansion emits the named steps or reports
the rule gap, and profiling reports the restricted site.

**Checked examples:** [`condition_search_explicit_decomposition.md`](https://github.com/clicklang/click/blob/master/mdtests/condition_search_explicit_decomposition.md)

### Available facts

**Form:** `assumption()`

**Expansion output.** `click expand` writes it; by hand, write it to close a
goal that is exactly an available fact without any search, typically after a
`rewrite`. Close the current goal when it follows directly from available facts:
the goal is itself a fact, or it is a conjunction whose every side follows this
way, or a disjunction one side of which does.

**Failure, checking, and tools:**

A conjunction or disjunction costs one lookup per side of the goal, and a
failure names the first side that is not available; lookup uses the shared
equality closure, including checked algebraic model aliases and typed
constructor and pure-call congruence, so known equal arguments denote equal
applications; prove other missing premises with `have` first.

An explicit `have separate(...)` can use the live ownership partition
immediately after `unfold`, including fixed-size fields fully contained in
different owned objects; it checks complete byte coverage and grants no new
ownership. `split()`, `left()` and `right()` were folded into this tactic and
are refused with that advice.

Lookup accepts representation-independent identity such as alpha-renamed
quantified binders, condition polarity, and certified identity of a resource
separation. It performs no function unfolding, implication extraction, or
cross-snapshot fact transport. Expansion leaves the step unchanged, and
profiling charges one simple leaf.

**Checked examples:** [`simple_tactics.md`](https://github.com/clicklang/click/blob/master/mdtests/simple_tactics.md)

### Extracting a fact

**Form:** `extract(P)`

**Expansion output.** `click expand` writes it; by hand, write it to state one
conjunct or consequent of a fact before a step that needs it spelled. Add `P` as
a sub-conjunction of an exact conjunction, by checked disjunction projection, by
bounded modus ponens from an available implication chain and checked antecedents
(including an alpha-equivalent quantified consequent), or by same-position
injectivity from an exact equality of one checked algebraic constructor.

Each leaf conjunct of a fact is already an available fact, so `extract` of a
leaf conjunct is accepted but adds nothing; every tactic, including
`assumption()` and an arithmetic certificate's premises, may cite it directly.

Between execution steps and after execution, a bare `extract(P)` adds `P` to
the current state exactly as `have P by { extract(P); }` does.

**Failure, checking, and tools:**

A noncomponent, missing antecedent, different constructor, or wrong field
position fails. A refusal names the requested proposition in its written
syntax, retaining parameter and proof-local names. Click follows an indexed,
checked derivation with no search; expansion is unchanged, and profiling
charges that derivation.

**Checked examples:** [`extract_refusal_keeps_written_parameter_names.md`](https://github.com/clicklang/click/blob/master/mdtests/extract_refusal_keeps_written_parameter_names.md), [`logical_tactics.rs`](https://github.com/clicklang/click/blob/master/src/surface/tests/tactic_tests/logical_tactics.rs), [`algebraic_symbolic_values.md`](https://github.com/clicklang/click/blob/master/mdtests/algebraic_symbolic_values.md)

### Context-free normalization

**Form:** `normalize()`

**Expansion output.** `click expand` writes it; by hand, write it to close a
goal that is true by evaluation alone, typically after `unfold` or `rewrite`.
It reads no facts, so it proves the same goal in every context.

**Accepts** a goal that is not itself a conjunction, disjunction, implication,
or quantifier, when evaluation makes it true:

- Every operation whose operands are all constants is evaluated: C machine
  arithmetic, bitwise operations, shifts, and division or remainder by a
  nonzero constant, all at the operand type's width; width and sign
  conversions, including `(uint64)` of an `int32` constant that `unfold` or
  `rewrite` substituted; exact `Integer` arithmetic and `to_integer` of a
  constant; and comparisons of constants.
- On symbolic terms, `x + 0`, `x - 0`, `x * 1`, and `x * 0` reduce, at C
  widths and for `Integer`.
- An equality, `<=`, or `>=` whose two sides are then the same term, up to
  renaming of bound variables, is true; so is `!=` between different
  constants.
- A `match` on a constructor selects its arm, and an equality between two
  applications of one algebraic constructor reduces to its fields.

**Outside it**, with what to write instead:

- A top-level `and`, `or`, implication, or quantifier: use `both`, prove one
  disjunct with `have` and close with `assumption()`, or `intro`.
- A goal that needs a fact, including a premise of the theorem: use
  `normalize() using { P; ... }`, `rewrite`, or `assumption()`.
- A pure function call: `unfold` it first; `normalize` leaves calls symbolic.
- Reordering, regrouping, or cancelling symbolic terms, such as
  `1 + to_integer(x) == to_integer(x) + 1`,
  `to_integer(x) - to_integer(x) == 0`, `2 * x == x + x`, or `x + 1 > x`: use
  `arithmetic()` or an arithmetic certificate.

`normalize` also accepts some goals beyond this list: sums and differences of
32-bit C words compare after reordering and cancellation, so `1 + x == x + 1`
and `x - x == 0` for an `int32` `x` close. That is not a documented
guarantee, so a refusal there, or of the same goal at another width, is not a
bug.

**Failure, checking, and tools:**

A refusal prints the goal after substitution. Click runs the deterministic
leaf check; expansion is unchanged, and profiling charges the normalized
expression. Smart tactics retain the corresponding `both`, disjunct proof and
`assumption()`, or `intro` proof.

**Checked examples:** [`simple_tactics.md`](https://github.com/clicklang/click/blob/master/mdtests/simple_tactics.md), [`normalize_evaluates_a_substituted_conversion.md`](https://github.com/clicklang/click/blob/master/mdtests/normalize_evaluates_a_substituted_conversion.md), [`normalize_does_not_reorder_integer_terms.md`](https://github.com/clicklang/click/blob/master/mdtests/normalize_does_not_reorder_integer_terms.md)

### Normalization with selected premises

**Form:** `normalize() using { P; ... }`

**Expansion output.** `click expand` writes it; by hand, write it only in an
explicit proof that must evaluate a goal under named conditions without search.
Reduce a proposition using explicitly cited conditions and graph-established
pointer and int32 equalities, including conditional-expression guards, then
close by context-free normalization.

**Failure, checking, and tools:**

Every premise must be exactly available and express a single condition or its
negation, including algebraic equality. Ambient equalities in the trusted kernel
graph include symbolic-pointer transitivity and supported same-snapshot load
congruence, plus explicit pointer-offset equality and addition congruence
(including equal displacements of ordinary C pointer parameters); explicit int32
equality, transitivity, and addition congruence are also available, including
propagation into same-width int32 scaled offsets.

Registered four-byte int32 reads also have congruence at equal offsets within
the same defining snapshot and storage block. For a top-level 64-bit read
equality, the cited conditions can also justify its recorded stored value: the
typed memory-history walk checks each effect, including the caller-owned ranges
recorded by a call, and requires a complete eight-byte value.

The local read-value rule crosses at most 64 history edges; a longer frame needs
an explicit intervening proof step. An overwritten or partially overwritten read
cannot reuse the old value. This adds no ambient frame search or read
permission. Explicitly cited equality between the exact Integer observations of
a `uint64` index and an `int32` index also establishes equal pointer offsets at
one common element width, including common base displacements.

A low-word equality is insufficient. Other scalar operations remain opaque, and
equality does not establish C signed definedness. Other unlisted conditions are
ignored. An unsuccessful graph query leaves equality unknown, never false. Every
cited premise is still validated, even if the graph already establishes the
goal.

A top-level conjunction, disjunction, or implication remaining after reduction
requires explicit structural construction. Reduction does not enter quantified
bodies, match-arm bodies, or range-fold binders; introduce or unfold those
first. Pure calls remain symbolic. Expansion retains the normalization step and
cited evidence; checking reconstructs the graph from the surrounding checked
proof context.

Work follows the selected expression and premises.

**Checked examples:** [`normalize_using.md`](https://github.com/clicklang/click/blob/master/mdtests/normalize_using.md), [`uint64_int32_exact_index_alias.md`](https://github.com/clicklang/click/blob/master/mdtests/uint64_int32_exact_index_alias.md), [`uint64_int32_owned_index_alias.md`](https://github.com/clicklang/click/blob/master/mdtests/uint64_int32_owned_index_alias.md), [`uint64_int32_low_word_is_not_address_equality.md`](https://github.com/clicklang/click/blob/master/mdtests/uint64_int32_low_word_is_not_address_equality.md)

### Arithmetic search

**Form:** `arithmetic()`

**Specialized.** Write it only for a bound that follows from the goal's own
terms, such as `(x & 255) <= 255`; it reads no fact. Plan and check a bounded
arithmetic certificate for the current comparison or equality, in the signed
`int32` family or in the mathematical `Integer` linear family.

The family is decided by the goal's own checked terms, never guessed from its
spelling, and the two never coerce into each other. For `int32`, affine terms
plus bounded products and constant remainder, shift, bit-mask, and sign-bit-flip
terms are supported; the latter also checks unsigned constant bounds from
explicit signed intervals, and sums `uint32` order premises over their
sign-bit-flipped operands, so `x < n` and `n <= 4u32` give `x < 4u32` as the
same `int32` chain would.

For `Integer`, the goal is a linear comparison or equality over Integer atoms,
including opaque pure-function applications and range folds.

**Failure, checking, and tools:**

The bare form lists no premises and reads no fact from the context, so it proves
only what follows from the goal's own terms, such as `(x & 255) <= 255`; a goal
that depends on a fact needs the `using` form, and a failure says so. An
unsupported operator, a possibly overflowing goal expression, or a
nonconsequence fails locally.

A goal recognized as `Integer` linear reports that fragment, not the `int32`
precondition. The planner runs once and expansion retains its checked structural
certificate.

**Checked examples:** [`pure_arithmetic_affine.md`](https://github.com/clicklang/click/blob/master/mdtests/pure_arithmetic_affine.md), [`pure_arithmetic_bounded_operations.md`](https://github.com/clicklang/click/blob/master/mdtests/pure_arithmetic_bounded_operations.md), [`arithmetic_on_an_unfold_refreshed_goal.md`](https://github.com/clicklang/click/blob/master/mdtests/arithmetic_on_an_unfold_refreshed_goal.md)

### Arithmetic with selected premises

**Form:** `arithmetic() using { P; ... }`

**Specialized.** Write it when `simp` misses an integer bound or equality,
listing the premises the bound follows from. Plan and check a bounded
certificate using only the exact listed premises; no ambient fact participates,
and a listed premise outside the goal's family is skipped rather than refused.

In the signed `int32` family, summed inequalities have positive coefficients;
bounded nonlinear terms use interval facts; one selected premise can be scaled
to a larger coefficient. A selected affine machine premise can also be
decomposed when the listed bounds prove every operation defined: `a <= 1000 - b`
(or `a == 1000 - b`) with `1 <= b; b <= 1000` gives `a <= 999`, and `a + b <=
1000` gives the same bound when both operands have safe listed ranges.

Expansion records the premise conversion as `affine_premise source left_evidence
right_evidence => P;`, with checked interval evidence for both expression roots.
Premise conversion also composes with a compound goal: safe listed bounds and `a
<= 2147483646 - b` establish `1 + a <= 2147483647 - b`.

Every decomposed premise and goal operation has independent interval evidence
from the original listed facts; an affine consequence cannot justify its own
definedness. Also checks pointer alignment and equal byte translations of one
listed pointer equality, including `p + 1 == arr + (i + 1)` from `p == arr + i`
and `i < n`.

Signed index sums are distributed only when the listed scalar bounds exclude
overflow. A goal spelled `>` or `>=` is read from the other side, so a bound
over a machine operation is planned in either orientation. A listed non-strict
bound and a disequality on the same two sides give the strict bound, which the
certificate records as `less_than_from_not_equal`.

A strict bound `i < n` bounds `i` by `2147483646` through `n`'s own `int32`
range when no premise bounds `n`, which the certificate records as
`int32_range`; a non-strict `i <= n` bounds `i` only by `2147483647`. In the
`Integer` linear family, any number of listed equalities participate: they are
eliminated, in the order written, each solved for the smallest atom it still
mentions, with exact integer cross multiplication and no division.

An equality goal must reduce away completely; an order goal is decided, after
that elimination, by at most two of the reduced inequalities, whether or not the
elimination changed the goal itself. A `uint64` or `int64` goal written `left <
right`, `left <= right` or `left == right` is proved through the exact Integer
observations of its operands. A comparison of observations is the native
comparison itself (see
[One form for comparisons of observations](../../internals/mathematical-integers.md#one-form-for-comparisons-of-observations)),
so each listed premise of that type is restated over its observations by
`assumption()`, a listed `not left < right` is read as `right <= left`, each
`uint64` value written beside a sum or difference has its type's range stated
by `uint64_to_integer_bounds`, each sum and difference in the premises and the
goal is shown to stay in range from the facts before it and observed by
`uint64_add_to_integer` or `uint64_subtract_to_integer`, the Integer claim is
proved in the `Integer` family, and `assumption()` concludes the goal. A listed
premise the proof does not hold is refused as an unavailable exact premise.

An equality goal takes its type from a listed order premise or a typed literal,
and is read this way only when both sides are sums and differences of plain
operands; an equality over a product, a shift or a mask is left to the other
families. An unsigned sum must not exceed the type; a signed one is shown
defined from both Integer bounds by `int64_add_defined_by_integer_bounds` or
`int64_subtract_defined_by_integer_bounds`, and a premise over a signed sum is
carried only once that sum is defined.

Expansion writes those steps out as `have` and `apply` steps with their
`Integer` certificates.

**Failure, checking, and tools:**

A 64-bit sum or difference the listed premises do not keep in range is refused
by name: where it may leave the type's range it is not the sum or difference of
its operands. An unavailable premise, unsupported relation, possible goal
overflow, or failed consequence fails locally. An `Integer` refusal names that
fragment and lists which premises were read as `Integer` linear claims and which
were skipped.

A goal coefficient an elimination pivot does not divide also fails locally:
concluding a multiple of the goal is not concluding the goal, and no certificate
node divides that factor back out. The planner scans only explicit premises and
emits a flat certificate; expansion directly rechecks that certificate without
planning again.

**Checked examples:** [`pure_arithmetic_affine.md`](https://github.com/clicklang/click/blob/master/mdtests/pure_arithmetic_affine.md), [`pure_arithmetic_bounded_operations.md`](https://github.com/clicklang/click/blob/master/mdtests/pure_arithmetic_bounded_operations.md), [`c_pointer_local_loop_invariant.md`](https://github.com/clicklang/click/blob/master/mdtests/c_pointer_local_loop_invariant.md), [`arithmetic_plans_a_greater_bound_on_an_operation.md`](https://github.com/clicklang/click/blob/master/mdtests/arithmetic_plans_a_greater_bound_on_an_operation.md), [`arithmetic_sharpens_a_bound_with_a_disequality.md`](https://github.com/clicklang/click/blob/master/mdtests/arithmetic_sharpens_a_bound_with_a_disequality.md), [`arithmetic_bounds_a_strict_lower_side_below_int32_max.md`](https://github.com/clicklang/click/blob/master/mdtests/arithmetic_bounds_a_strict_lower_side_below_int32_max.md), [`arithmetic_eliminates_integer_equalities.md`](https://github.com/clicklang/click/blob/master/mdtests/arithmetic_eliminates_integer_equalities.md), [`arithmetic_refuses_an_unchained_integer_equality.md`](https://github.com/clicklang/click/blob/master/mdtests/arithmetic_refuses_an_unchained_integer_equality.md), [`a_size_t_loop_stepping_by_two_closes_with_arithmetic.md`](https://github.com/clicklang/click/blob/master/mdtests/a_size_t_loop_stepping_by_two_closes_with_arithmetic.md), [`a_uint64_sum_that_may_wrap_is_not_arithmetic.md`](https://github.com/clicklang/click/blob/master/mdtests/a_uint64_sum_that_may_wrap_is_not_arithmetic.md), [`arithmetic_proves_int64_order_goals.md`](https://github.com/clicklang/click/blob/master/mdtests/arithmetic_proves_int64_order_goals.md), [`an_int64_sum_that_may_overflow_is_not_arithmetic.md`](https://github.com/clicklang/click/blob/master/mdtests/an_int64_sum_that_may_overflow_is_not_arithmetic.md), [`arithmetic_reduces_order_premises_under_an_untouched_goal.md`](https://github.com/clicklang/click/blob/master/mdtests/arithmetic_reduces_order_premises_under_an_untouched_goal.md), [`arithmetic_compound_premise_and_goal.md`](https://github.com/clicklang/click/blob/master/mdtests/arithmetic_compound_premise_and_goal.md), [`arithmetic_compound_wrapping_premise.md`](https://github.com/clicklang/click/blob/master/mdtests/arithmetic_compound_wrapping_premise.md)

### Arithmetic certificates

**Form:** `arithmetic_certificate { premise ...; conclusion N; }` / `arithmetic_certificate signed_int32 { ... }` / `arithmetic_certificate rules { ... }`

**Expansion output.** `click expand` writes it; a person writes `arithmetic()
using` instead and lets expansion produce the certificate. Check a typed
arithmetic-certificate envelope. The unsuffixed form is the mathematical
`Integer` family; in it, `negated_goal => P;` assumes the integer negation of a
bound goal, `divide N by g => P;` divides a non-strict bound by a positive
common factor of its coefficients and rounds its constant, and a contradiction
such as `1 <= 0` at the conclusion proves the goal
(`mdtests/integer_certificate_refutation_and_rounding.md`).

`signed_int32` selects checked signed-machine arithmetic, including
`interval_narrowed_cast`, which treats a C conversion into `int8`, `uint8`,
`int16` or `uint16` of a 32-bit-word operand as that operand when the operand's
checked interval lies inside the destination range
(`mdtests/a_conversion_in_range_is_its_operand_in_a_signed_certificate.md`),
while `rules` selects pointer translation/alignment/tagged-word, finite-float
reflexivity, `int32` / `int64` definedness, exact `Integer` product-bound nodes,
truncating quotient/remainder bounds, and range-checked modulo cast identities.

Unsigned byte and 16-bit readbacks with canonical low-bit masks retain their
observations when promoted to a 32-bit word; both source bounds remain explicit.
`integer_product_bounds bounds [i, j, k, l] => T <= x * y;` (or `x * y <= T`)
uses four constant-endpoint bounds in left-lower/upper then right-lower/upper
order; see the product-bound rule below.

`integer_division_bounds bounds [i, j, k, l] => T <= truncating_quotient(n, d);`
(or an upper bound, or `truncating_remainder`) checks four explicit
constant-endpoint numerator/divisor bounds and requires the divisor interval to
exclude zero; see [division
bounds](../../internals/mathematical-integers.md#truncating-division-bounds).

`integer_quotient_bound bounds [i, j] => b <= truncating_quotient(n, d);` (or an
upper bound) checks the exact scaled numerator bound followed by `1 <= d`; see
[scaled quotient
bounds](../../internals/mathematical-integers.md#scaled-positive-divisor-quotient-bounds).
`integer_bound_exclusion bounds [i] => x != c;` excludes a constant strictly
outside one named non-strict bound; see [bound
exclusion](../../internals/mathematical-integers.md#bounds-excluding-constants).

`integer_polynomial_identity bounds [] => L == R;` checks a bounded mathematical
Integer ring identity with non-ring roots opaque; `integer_quotient_shift bounds
[i, j] => truncating_quotient(x + d * k, d) == truncating_quotient(x, d) + k;`
requires a positive constant divisor and exact named nonnegative bounds on `x`
and `k`; see [polynomial and quotient
rules](../../internals/mathematical-integers.md#bounded-polynomial-identities-and-quotient-shifts).

`integer_relation_transport bounds [i, j] => P;` uses a named Integer equality
to replace one whole operand of a named equality or non-strict bound; it checks
relation kind, polarity, and operand identities without recursive substitution.
`integer_cast_identity bounds [i, j] => to_integer(cast_value) ==
to_integer(source_value);` checks two named bounds against the typed cast
destination's range; see [the cast identity
rule](../../internals/mathematical-integers.md#range-checked-modulo-cast-identities).

`integer_operation_identity bounds [i, j] => to_integer(a + b) ==
to_integer(a) + to_integer(b);` (or `-`) checks two named constant bounds on
the Integer result against the range of the `int`, `unsigned int`, `int64` or
`uint64` operation. In the unsuffixed family, `type_range => MIN <=
to_integer(v);` (or `to_integer(v) <= MAX`) states a machine type's range, and
a premise comparing exact observations of one machine type is also available
from its native comparison. See [in-range sums and
differences](../../internals/mathematical-integers.md#in-range-machine-sums-and-differences).

`int64_defined bounds [i, ...] => defined(a + b);` (or `a - b`) proves `int64`
definedness: each operand's range is the width range of its root constructor (a
constant, or a value widened from `int` or `unsigned int`; any other `int64`
term has the whole `int64` range), narrowed by the listed premises, each a
constant `int64` order or equality fact on an operand, and the exact result
range must stay inside `int64`.

`int32_defined bounds [i, ...] => defined(a + b);` is the same checker at
`int32`: a constant operand is itself and any other `int32` term (including a
promoted `char` or `short`) has the whole `int32` range, the listed premises are
constant `int32` facts, and the result must stay inside `int32`.

A refusal names the result range found.

**Failure, checking, and tools:**

Every result is recomputed, references are bounded by the explicit premise/node
lists, and every premise must be exactly available. Explicit certificates never
invoke planning or the legacy whole-goal checker. Machine families have no
implicit coercion between signed, unsigned, pointer, and float terms: source
conversions must be present and checked.

Cross-domain proofs compose through separately checked bridge
theorem/application steps; a certificate family never coerces another family’s
proposition. Snapshot changes and conjunction members require explicit `at(...)`
provenance or `extract(...)` steps. Expansion emits the same certificate that
`verify`, `profile`, and `audit` inspect, so all four tools agree on the checked
proof.

**Checked examples:** [`arithmetic_certificate_surface.md`](https://github.com/clicklang/click/blob/master/mdtests/arithmetic_certificate_surface.md), [`signed_int32_arithmetic_certificate_surface.md`](https://github.com/clicklang/click/blob/master/mdtests/signed_int32_arithmetic_certificate_surface.md), [`signed_int32_certificate_composition.md`](https://github.com/clicklang/click/blob/master/mdtests/signed_int32_certificate_composition.md), [`aligned_explicit_arithmetic.md`](https://github.com/clicklang/click/blob/master/mdtests/aligned_explicit_arithmetic.md), [`tagged_pointer_explicit_arithmetic.md`](https://github.com/clicklang/click/blob/master/mdtests/tagged_pointer_explicit_arithmetic.md), [`int64_defined_from_bounds.md`](https://github.com/clicklang/click/blob/master/mdtests/int64_defined_from_bounds.md), [`int32_defined_from_bounds.md`](https://github.com/clicklang/click/blob/master/mdtests/int32_defined_from_bounds.md), [`integer_product_bounds.md`](https://github.com/clicklang/click/blob/master/mdtests/integer_product_bounds.md), [`integer_division_bounds.md`](https://github.com/clicklang/click/blob/master/mdtests/integer_division_bounds.md), [`integer_cast_identity_unsigned_subword_promotion.md`](https://github.com/clicklang/click/blob/master/mdtests/integer_cast_identity_unsigned_subword_promotion.md), [`an_in_range_machine_difference_is_its_integer_difference.md`](https://github.com/clicklang/click/blob/master/mdtests/an_in_range_machine_difference_is_its_integer_difference.md)

### Rewriting

**Form:** `rewrite(P)`

**Core.** Rewrite the current proposition, including memory-resource ranges and
algebraic-constructor fields, with exact available equality `P`. Native
equalities preserve signed and unsigned scalar comparison kinds and widths,
including full-width 64-bit order and machine observations inside mathematical
`Integer` bounds.

When exact substitution misses an atomic native equality goal, its two operands
may match the cited left-hand expression through checked corresponding read
leaves, for both 32-bit and 64-bit reads inside matching arithmetic operators.
Alias and snapshot evidence comes from the shared read-equality checker;
incompatible read kinds, changed cells, and differing operators do not match.

This comparison visits only the cited expression and the two goal operands.
Mathematical `Integer` equality substitutes exact occurrences inside products,
sums, negations, differences, truncating quotient/remainder terms and
pure-function arguments. Internal fold/match binders are refused; an exact
whole-fold occurrence can still be replaced.

A pointer equality rewrites the base of an explicit `viewable(...)` claim while
preserving its memory snapshot and byte extent. A cited shifted view whose
extent is `(i + 4) - i` also covers the same address with a literal four-byte
extent; constant endpoint differences are compared in the extent's own modular
arithmetic.

It also rewrites the addresses of loads read through the pointer, including byte
reads observed with `to_integer` and a pointer that is itself loaded
(`o->in->cells[2]` under `o->in == a`); it keeps the read’s observed snapshot
and load type. An equality whose left side is a whole symbolic pointer (`p ==
q`, `p == 0`) replaces that pointer everywhere, including inside `(uint64)p`;
null's address is the integer zero.

An integer equality whose left side is a composite term, such as a pure-function
application, is not substituted under the binder of a `match` arm: an unfolded
`match` it cannot enter is left exactly as it was.

**Failure, checking, and tools:**

An absent equality, wrong direction with no exact match, or ill-typed rewrite
fails. Click performs that rewrite only; expansion is unchanged, and profiling
charges the affected expression.

**Checked examples:** [`simple_tactics.md`](https://github.com/clicklang/click/blob/master/mdtests/simple_tactics.md), [`equality_rewrite_scalar_bounds.md`](https://github.com/clicklang/click/blob/master/mdtests/equality_rewrite_scalar_bounds.md), [`integer_equality_rewrite.md`](https://github.com/clicklang/click/blob/master/mdtests/integer_equality_rewrite.md), [`algebraic_symbolic_values.md`](https://github.com/clicklang/click/blob/master/mdtests/algebraic_symbolic_values.md), [`rewrite_through_a_loaded_pointer_field.md`](https://github.com/clicklang/click/blob/master/mdtests/rewrite_through_a_loaded_pointer_field.md), [`rewrite_pointer_inside_integer_read.md`](https://github.com/clicklang/click/blob/master/mdtests/rewrite_pointer_inside_integer_read.md), [`rewrite_pointer_null_into_an_address.md`](https://github.com/clicklang/click/blob/master/mdtests/rewrite_pointer_null_into_an_address.md), [`rewrite_pointer_into_a_shifted_byte_view.md`](https://github.com/clicklang/click/blob/master/mdtests/rewrite_pointer_into_a_shifted_byte_view.md), [`rewrite_keeps_a_match_it_cannot_substitute_through.md`](https://github.com/clicklang/click/blob/master/mdtests/rewrite_keeps_a_match_it_cannot_substitute_through.md)

### Introducing a binder or premise

**Form:** `intro()`

**Core.** For an implication, negation, or universal goal, add the antecedent or
named binder and continue with the body goal. A universal's variable keeps the
name its quantifier wrote; if that name is already in scope it shadows the older
one, which stays readable as `outer.name`. That includes a range quantifier's
variable in a `have` stated between C statements
([`intro_names_a_range_variable_in_a_have_between_statements.md`](https://github.com/clicklang/click/blob/master/mdtests/intro_names_a_range_variable_in_a_have_between_statements.md)).

**Failure, checking, and tools:**

Any other goal shape fails. Click checks the one introduction rule; expansion is
unchanged, and profiling charges one leaf.

**Checked examples:** [`copy_n_segment_invariant.md`](https://github.com/clicklang/click/blob/master/mdtests/copy_n_segment_invariant.md)

### Naming an introduced binder

**Form:** `intro() as name`

**Specialized.** Write it when the quantifier's own variable name would clash
with or obscure a name the proof uses. For a goal written `forall (x: T) { ...
}` or `(lo..hi).all(|x| { ... })`, introduce the bound variable under `name`
instead of `x`, and continue with the body goal written in terms of `name`.

The proof chooses its own name where bare `intro()` takes the one the
proposition was written with.

**Failure, checking, and tools:**

`name` must be new: a parameter, local, proof binding, or name the body already
reads is refused, and nothing is shadowed. An implication or negation goal is
refused, since it introduces a fact and facts have no names; after a range
quantifier's variable, the next `intro()` introduces its range guard.

Click checks the same one introduction rule; expansion is unchanged.

**Checked examples:** [`intro_as_names_the_introduced_variable.md`](https://github.com/clicklang/click/blob/master/mdtests/intro_as_names_the_introduced_variable.md), [`intro_as_requires_a_new_name.md`](https://github.com/clicklang/click/blob/master/mdtests/intro_as_requires_a_new_name.md), [`intro_as_names_a_range_quantifier_variable.md`](https://github.com/clicklang/click/blob/master/mdtests/intro_as_names_a_range_quantifier_variable.md)

### Finite enumeration

**Form:** `enumerate()`

**Expansion output.** `click expand` writes it; by hand, write it only to close
a constant-bounded universal from instances you state one by one. Close a
constant-bounded universal from exact in-range instances or context-free vacuous
guards, in range order; an instance whose guard is constant true may be held as
its conclusion.

**Failure, checking, and tools:**

An unbounded guard or missing instance fails. Click checks the explicit finite
table with work proportional to it; expansion is unchanged, and profiling
reports that work.

**Checked examples:** [`logical_tactics.rs`](https://github.com/clicklang/click/blob/master/src/surface/tests/tactic_tests/logical_tactics.rs)

### Contradictions

**Form:** `contradiction(P)`

**Core.** Close the goal from exact `P` plus exact `not P`, the opposite
polarity of the same total C condition, or a context-free proof that `not P` is
true. A comparison and its arithmetic negation, such as `x < 0` held beside `x
>= 0`, also count, in every order family (`int32`, the 64-bit machine orders
such as `x < 32u64` beside `x >= 32u64`, and `Integer`): they are two different
lowered conditions rather than one condition at both polarities, and the
negation is recognized through the fixed list of equivalent spellings the
explicit closers share, by exact lookup rather than search.

**Failure, checking, and tools:**

A missing exact `P`, or a noncontradictory opposite, fails. A merely tighter
bound such as `x >= 1` is not the negation of `x < 0` and does not close the
goal. Click performs indexed lookups and at most one context-free normalization;
expansion is unchanged, and profiling charges one leaf.

**Checked examples:** [`surface_syntax.rs`](https://github.com/clicklang/click/blob/master/src/surface/tests/surface_syntax.rs),
[`contradiction_opposite_comparison.md`](https://github.com/clicklang/click/blob/master/mdtests/contradiction_opposite_comparison.md),
[`uint64_branch_negation_refutes_the_other_arm.md`](https://github.com/clicklang/click/blob/master/mdtests/uint64_branch_negation_refutes_the_other_arm.md)

### Universal instantiation

**Form:** `instantiate(F, value)`

**Specialized.** Write it to use a universal fact at one value when `simp` does
not choose that value. Specialize exact universal fact `F` at `value` when each
instantiated guard is directly available through the shared equality-backed
lookup, and add the conclusion. The guards are fixed by `F` and `value`, so this
is one availability lookup per guard conjunct; nothing is unfolded or searched.

Equivalent operand spellings count as the same guard. An unguarded `F` needs no
fact at all.

**Failure, checking, and tools:**

An absent `F`, a bad binder value, or a guard unavailable to that lookup fails,
naming the guard; prove it first with `have` or use the `using` form. Expansion
is unchanged, and profiling charges the guards and result.

**Checked examples:** [`instantiate_without_using_finds_its_guards.md`](https://github.com/clicklang/click/blob/master/mdtests/instantiate_without_using_finds_its_guards.md), [`instantiate_without_using_names_a_missing_guard.md`](https://github.com/clicklang/click/blob/master/mdtests/instantiate_without_using_names_a_missing_guard.md)

### Instantiation with selected premises

**Form:** `instantiate(F, value) using { P; ... }`

**Expansion output.** `click expand` writes it; by hand, prefer the bare form,
which finds its guards. Specialize exact universal fact `F` at `value`,
discharge guards from only the listed premises, and add the conclusion. The
binder is `int32` or `uint64`, and `value` has the binder's type.

**Failure, checking, and tools:**

An absent `F`, bad binder value, or undischarged guard fails. Click performs the
named instantiation; expansion is unchanged, and profiling charges the explicit
premises and result.

**Checked examples:** [`logical_tactics.rs`](https://github.com/clicklang/click/blob/master/src/surface/tests/tactic_tests/logical_tactics.rs), [`instantiate_a_universal_over_uint64.md`](https://github.com/clicklang/click/blob/master/mdtests/instantiate_a_universal_over_uint64.md)

### Theorem application

**Form:** `apply(theorem(args))`

**Core.** Apply a verified global theorem and select its proposition premises
from context. A premise that is not an available fact is proved as a `have` by
`auto`, spelled as the theorem's `requires` with the written arguments
substituted, and then cited.

**Failure, checking, and tools:**

An unknown theorem, type mismatch, or bounded premise-selection miss fails
without changing resources; a premise `auto` cannot prove keeps the refusal that
names it. Click checks the selected application; expansion adds those `have`s
and `using`, and profiling reports search and leaves.

**Checked examples:** [`pure_theorem_apply.md`](https://github.com/clicklang/click/blob/master/mdtests/pure_theorem_apply.md), [`apply_proves_a_missing_premise_by_auto.md`](https://github.com/clicklang/click/blob/master/mdtests/apply_proves_a_missing_premise_by_auto.md)

### Theorem application with selected premises

**Form:** `apply(theorem(args)) using { P; ... }`

**Expansion output.** `click expand` writes it; by hand, prefer the bare form,
which selects or proves its premises; list them only to pin the proof down.
Apply a verified global theorem using exactly the listed premises and add its
guarantees. Mathematical `Integer` arguments may use explicit machine
observations such as `to_integer(a)`; fixed-state capture checks arithmetic
evaluation guards and preserves `old`/`at` selectors. Bare `apply` also selects
known evaluation guards for expressions nested inside model arguments, such as
`defined(x - 1)` for `Count::At(x - 1)`. These are selected argument conditions,
not additional theorem requirements; removing their evidence from an expanded
`using` list can make the application fail.

Heap observations follow logical specification read semantics and grant no
access authority. Arguments are substituted simultaneously from the caller
bindings. Guarantees are every `ensures` of the theorem at the given arguments,
including when one of them is the current goal. In that case the goal closes
unless other written steps follow, as for any tactic that adds a fact.

A listed equality, and an equality requirement, is matched in either
orientation: `have a == b` discharges a requirement that instantiates to `b ==
a`.

**Failure, checking, and tools:**

Any missing requirement or mismatched argument fails. Click checks the exact
application with no search; expansion is unchanged, and profiling charges its
explicit input and guarantees.

**Checked examples:** [`produced_population_count_in_ensured_predicate.md`](https://github.com/clicklang/click/blob/master/mdtests/produced_population_count_in_ensured_predicate.md), [`apply_keeps_sibling_conclusions_when_one_is_the_goal.md`](https://github.com/clicklang/click/blob/master/mdtests/apply_keeps_sibling_conclusions_when_one_is_the_goal.md), [`apply_does_not_supply_a_conclusion_its_theorem_lacks.md`](https://github.com/clicklang/click/blob/master/mdtests/apply_does_not_supply_a_conclusion_its_theorem_lacks.md)

### Unfolding pure functions

**Form:** `unfold(function(args))`

**Core.** Expose one defining equation for the exact pure-function call at the
current proof state and refresh the current proposition through that one layer.
Integer arguments resolve in their lexical proof scope, including `intro` and
`obtain` binders; a proof local shadows a same-named theorem parameter.

**Failure, checking, and tools:**

An unknown function or argument mismatch fails. Recursive calls in the body stay
opaque; expansion is unchanged, and profiling charges the arguments and one body
layer.

**Checked examples:** [`pure_function_unfold.md`](https://github.com/clicklang/click/blob/master/mdtests/pure_function_unfold.md)

### Peeling a pure function

**Form:** `peel(function(args)) using { P; ... }`

**Specialized.** Write it to open one step of a range-fold function, such as a
sum over an array prefix, in an induction over its end. For an `Integer`-valued
function whose body is exactly a range fold over a symbolic range, open the
range-fold law the listed guards select, stated over the call itself: with the
empty-range guard, `f(args) == <initial>`; with `lo <= hi - 1` and `hi - 1 <
2147483647`, `f(.., hi) == f(.., hi - 1) + <body at hi - 1>`.

A `uint64` range has the same two laws with unsigned order, and its append guard
is `hi - 1 < 18446744073709551615u64`. A call whose range the kernel already
reduced, because its endpoints are constants, gives its defining equation with
no guard. The single produced fact is that equation, and the goal is refreshed
through it, so a range fact about a whole array range is provable by the
existing `induct(hi)`.

**Failure, checking, and tools:**

`peel` takes a pure-function application and requires its `using` list; `unfold`
takes no `using`. The step is a derived use of the two kernel fold laws: the raw
defining equation and its predecessor instance are the law's own premises and
stay inside the step. Every guard must be an exact listed premise; nothing is
searched, and an undecided range is refused with what each form still wants.

The append form needs the fold's end to be a parameter that the fold reads
nowhere else. Expansion is unchanged, and profiling charges one law instance.

**Checked examples:** [`unfold_fold_function_empty_range.md`](https://github.com/clicklang/click/blob/master/mdtests/unfold_fold_function_empty_range.md), [`unfold_fold_function_appends_last_cell.md`](https://github.com/clicklang/click/blob/master/mdtests/unfold_fold_function_appends_last_cell.md), [`fold_function_is_nonnegative_by_induction.md`](https://github.com/clicklang/click/blob/master/mdtests/fold_function_is_nonnegative_by_induction.md)

### Constructor matches

**Form:** `match value [ensuring { ... }] { Type::Variant(fields) => { ... } ... }`

**Core.** In a pure proposition proof (including structural-induction arms), or
at any execution frontier the proof has reached — unchanged function entry,
after executed statements, or a loop's `preserve` body — split an ADT of any
width into exhaustive execution proofs, one arm per constructor.

The live arms are joined by a balanced tree of frontier splits, so three or more
constructors need no extra wrapper functions. Fields are fresh typed, arm-local
symbolic values, in scope for the whole arm including the arms of a `branch` or
proof-level `if` written inside it and the body of a `have`; nested entry
matches are supported. An arm that reaches function exit keeps its fields on
that finished path only: the other arm of an enclosing proof `if` starts in the
scope the `if` was written in, and may bind the same names
(`mdtests/each_proof_if_arm_may_reuse_a_match_binding_name.md`,
`mdtests/a_match_binding_does_not_reach_the_other_proof_if_arm.md`).

Where the arms end follows the region: in a function proof with nothing written
after the `match`, each live arm must reach function exit and the arms are
joined there; with tactics written after it, every live arm must end at the same
program point in the same state, and the arms rejoin there so those tactics are
checked once, without the constructor facts or fields of any arm; in a loop's
`preserve` body with nothing written after the `match`, each live arm must
execute one complete iteration on its own path — restoring the loop binder,
closing the invariants and satisfying the structural descent at the body's end
or at a `continue`, or leaving through a `break`, which owes none of those.

After execution the `match` is decided on each outcome path, as a proof `if`
or `cases` is there: each path takes only the arm its own constructor case
selects, and a path on which more than one constructor is live forks into
one path per live arm. Each live arm finishes its own path
(`mdtests/match_after_execution_finishes_each_arm.md`), and with more than one
live arm, tactics written after the `match` are refused, since they would be
checked once per arm (`mdtests/match_after_execution_that_would_fork_is_refused.md`).
A `match` written inside an arm of a post-execution `if` or `cases` is
decided per outcome path in the same way, with the arm's field bindings
(`mdtests/a_match_in_a_post_execution_if_arm_takes_each_paths_arm.md`,
`mdtests/a_match_in_a_post_execution_cases_arm_takes_each_paths_arm.md`).
Tactics written after it in the same arm are part of that arm, so they
continue each path, as after a nested `if`
(`mdtests/tactics_after_a_nested_post_execution_match_continue_each_path.md`).
A `match` with `ensuring`, or with an arm that is a lone `contradiction`,
splits once at the exit frontier instead, on the facts every outcome path
shares, and so does a `match` whose scrutinee has no checked value on some
path.

Tactics written after a `match` in a `preserve` body are checked once:
straight-line arms that end in one state rejoin as in a function body, and two
arms still live at one program point that end apart are refused
(`mdtests/loop_body_proof_match_shared_continuation.md`). With `ensuring`, arms
that end apart rejoin inside the body, as the arms of a `branch` do, and those
tactics are checked once on the one path that leaves the `match`
(`mdtests/loop_body_proof_match_ensuring_rejoins.md`); a proof `if ... ensuring`
in a `preserve` body rejoins the same way.

The constructor equation is an entry assumption of the whole function only when
the `match` ran before any C step. Pure arms prove the same current goal under
fresh, typed payload bindings and the constructor equation; they add no
induction hypothesis and accept no `ensuring` clause.

Payload names are local to the written arm, including when tactics follow the
match. The kernel reduces the goal to universally quantified constructor
implications and checks their complete conjunction. An impossible arm may
consist of `contradiction(proposition)` naming an exact fact and its negation in
that case; the remaining live arms are split and joined normally, and a sole
live arm runs on the parent frontier without a join.

**Failure, checking, and tools:**

Missing, duplicate, wrong-type/arity, or escaping fields fail. Matching grants
no memory: each live arm must independently unfold and restore its owned
resources. Excluded arms retain checked contradictions, not simulated C
outcomes. Expansion retains and checks every arm. Arms that end in different
states rejoin through `ensuring { fact ...; owns ...; }`, written after the
scrutinee, exactly as the arms of a proof `if ... ensuring` do; a `match` over
more than two constructors is joined pairwise through the same interface.

Without `ensuring`, arms that end in different states are refused. Exclusion
after local proof prefixes and all-impossible matches remain unsupported.

**Checked examples:** [`proof_match_resource.md`](https://github.com/clicklang/click/blob/master/mdtests/proof_match_resource.md), [`proof_match_three_constructors.md`](https://github.com/clicklang/click/blob/master/mdtests/proof_match_three_constructors.md), [`proof_match_four_constructors.md`](https://github.com/clicklang/click/blob/master/mdtests/proof_match_four_constructors.md), [`proof_match_live_arms_beside_an_excluded_one.md`](https://github.com/clicklang/click/blob/master/mdtests/proof_match_live_arms_beside_an_excluded_one.md), [`match_bindings_in_branch_arm.md`](https://github.com/clicklang/click/blob/master/mdtests/match_bindings_in_branch_arm.md), [`proof_match_after_c_step.md`](https://github.com/clicklang/click/blob/master/mdtests/proof_match_after_c_step.md), [`loop_body_proof_match.md`](https://github.com/clicklang/click/blob/master/mdtests/loop_body_proof_match.md), [`loop_body_proof_match_two_live_arms.md`](https://github.com/clicklang/click/blob/master/mdtests/loop_body_proof_match_two_live_arms.md), [`loop_body_proof_match_shared_continuation.md`](https://github.com/clicklang/click/blob/master/mdtests/loop_body_proof_match_shared_continuation.md), [`proof_match_arms_rejoin.md`](https://github.com/clicklang/click/blob/master/mdtests/proof_match_arms_rejoin.md), [`proof_match_arms_must_rejoin.md`](https://github.com/clicklang/click/blob/master/mdtests/proof_match_arms_must_rejoin.md), [`proof_match_three_arms_rejoin.md`](https://github.com/clicklang/click/blob/master/mdtests/proof_match_three_arms_rejoin.md), [`proof_match_ensuring_rejoins.md`](https://github.com/clicklang/click/blob/master/mdtests/proof_match_ensuring_rejoins.md), [`proof_match_ensuring_three_constructors.md`](https://github.com/clicklang/click/blob/master/mdtests/proof_match_ensuring_three_constructors.md), [`pure_match_constructor_cases.md`](https://github.com/clicklang/click/blob/master/mdtests/pure_match_constructor_cases.md), [`pure_match_in_induction_arm.md`](https://github.com/clicklang/click/blob/master/mdtests/pure_match_in_induction_arm.md), [`pure_match_typed_payloads.md`](https://github.com/clicklang/click/blob/master/mdtests/pure_match_typed_payloads.md)

### Scalar induction

**Form:** `induct(n) as ih`

**Core.** As the first step of a pure theorem over an `int32` or `uint64` parameter
`n`, introduce a strong induction hypothesis named `ih`. The signed measure
requires a nonnegative domain; the unsigned measure has that domain intrinsically.

**Failure, checking, and tools:**

A later position, unsupported parameter type, or unproved signed nonnegative domain fails. Click
opens the induction rule; expansion is unchanged, and profiling charges the
structural setup.

**Checked examples:** [`pure_induction_countdown.md`](https://github.com/clicklang/click/blob/master/mdtests/pure_induction_countdown.md)
and [`uint64_measure_induction_counts_a_range_fold.md`](https://github.com/clicklang/click/blob/master/mdtests/uint64_measure_induction_counts_a_range_fold.md).

### Algebraic induction

**Form:** `induct(xs) as ih { Type::Variant(fields) => { ... } ... }`

**Core.** Prove a pure theorem for a recursive algebraic parameter by exhaustive
constructor cases; each immediate recursive field admits `ih(field)`, and
`ih(field, other, ...)` states the theorem at that field and any well-typed
terms in the remaining parameter positions.

**Failure, checking, and tools:**

A missing, duplicate, unknown, or wrong-arity arm fails. Bindings are arm-local,
and `ih` rejects nonrecursive or non-immediate values in the inducted position,
a parameter list of the wrong length, and an instantiation whose substituted
requirements are unavailable. Click checks every arm; expansion recurses through
the arm certificates.

**Checked examples:** [`algebraic_structural_induction.md`](https://github.com/clicklang/click/blob/master/mdtests/algebraic_structural_induction.md), [`algebraic_structural_induction_generalizes_parameters.md`](https://github.com/clicklang/click/blob/master/mdtests/algebraic_structural_induction_generalizes_parameters.md)

### Induction hypothesis application

**Form:** `apply(ih(m))`

**Core.** Select explicit proofs of `m < n` and the theorem requirements at `m`,
and `0 <= m` for a signed measure, then instantiate the local induction hypothesis. Under a
structural `induct` the obligations are instead the theorem's requirements at
the spelled parameter list, and the descent is the inducted argument naming a
field of the current arm.

**Failure, checking, and tools:**

A bounded proof-selection miss, nondecreasing argument, or violated requirement
fails. Click checks the selected operations; expansion adds any needed `have`
steps and a `using` block.

**Checked examples:** [`pure_induction_countdown.md`](https://github.com/clicklang/click/blob/master/mdtests/pure_induction_countdown.md)

### Induction hypotheses with selected premises

**Form:** `apply(ih(m)) using { P; ... }`

**Expansion output.** `click expand` writes it; by hand, prefer the bare form,
which proves the decrease and requirements. Instantiate the local induction
hypothesis from exactly the listed strict-decrease and substituted-requirement
obligations, including nonnegativity for a signed measure.

**Failure, checking, and tools:**

A missing exact obligation, wrong hypothesis, or mismatched argument fails.
Click performs one local instantiation with no premise search; expansion is
unchanged.

**Checked examples:** [`pure_induction_countdown_explicit.md`](https://github.com/clicklang/click/blob/master/mdtests/pure_induction_countdown_explicit.md)

### Intermediate facts

**Form:** `have P by { ... }`

**Core.** Open a nested goal `P`; on success, add `P` to the surrounding context
without changing its execution frontier. `have P;` without a proof is `have P by
simp();`, and a one-step proof may drop the braces: `have P by T(args);`. `have P
by auto();` executes no C: it tries the solver, which refutes the integer negation
of a linear `Integer` bound from the facts connected to `P` and applies the
result as one `arithmetic_certificate`, then `simp`
([`have_by_auto_refutes_a_linear_bound.md`](https://github.com/clicklang/click/blob/master/mdtests/have_by_auto_refutes_a_linear_bound.md)).

Connected `int32`, `int64` and `uint64` order facts are carried to `Integer` by
their bridge theorems, and `uint64` values get their type range from
`uint64_to_integer_bounds`; only the bridges the certificate cites are kept
([`auto_carries_machine_orders_to_integer.md`](https://github.com/clicklang/click/blob/master/mdtests/auto_carries_machine_orders_to_integer.md)).

A `uint64` or `int64` order goal, or an `int32` `<=` goal, is proved through its
`Integer` reading and carried back by the type's `to_integer_..._implies_...`
theorem
([`auto_proves_a_machine_order_through_integer.md`](https://github.com/clicklang/click/blob/master/mdtests/auto_proves_a_machine_order_through_integer.md)),
and an `Integer` equality goal from both of its bounds
([`auto_proves_an_integer_equality_from_both_bounds.md`](https://github.com/clicklang/click/blob/master/mdtests/auto_proves_an_integer_equality_from_both_bounds.md)).

A goal `defined(a + b)` or `defined(a - b)` over `int32` or `int64` is proved
from both `Integer` bounds of the exact result by the type's
`..._defined_by_integer_bounds` theorem
([`auto_proves_signed_addition_defined.md`](https://github.com/clicklang/click/blob/master/mdtests/auto_proves_signed_addition_defined.md)),
and each `to_integer(a + b)` or `to_integer(a - b)` in the goal is observed term
by term: a signed operation once it is defined, by `int32_add_to_integer` and
its relatives, and a `uint64` one once it does not wrap, by
`uint64_add_to_integer` or `uint64_subtract_to_integer`
([`auto_observes_an_operation_term_by_term.md`](https://github.com/clicklang/click/blob/master/mdtests/auto_observes_an_operation_term_by_term.md)).

Machine equality facts are carried by rewriting, each observed value gets its
type range from `int32_to_integer_bounds`, `int64_to_integer_bounds` or
`uint64_to_integer_bounds`, an `int32`, `int64` or `uint64` equality goal is
proved as its observed reading once both sides are shown defined, splitting an
equality into its two bounds when needed, and a conjunction goal is split
([`auto_proves_a_conservation_equation.md`](https://github.com/clicklang/click/blob/master/mdtests/auto_proves_a_conservation_equation.md)).

When the solver and `simp` both miss, `auto` searches chains of at most three
`rewrite` steps by the equalities connected to `P`, machine, `Integer` and
algebraic alike, each in either direction, and closes the rewritten goal by
`assumption`, `normalize`, the direct logical closer or, a few times per search,
`simp`.

Each rewrite is a checked step, and the search offers at most 64 equalities,
those that rewrite `P` itself first, and tries at most 256 rewrites, so a large
connected component fails promptly
([`auto_rewrites_a_constructor_term_to_its_model.md`](https://github.com/clicklang/click/blob/master/mdtests/auto_rewrites_a_constructor_term_to_its_model.md),
[`auto_refuses_a_constructor_rewrite_that_does_not_close.md`](https://github.com/clicklang/click/blob/master/mdtests/auto_refuses_a_constructor_rewrite_that_does_not_close.md)).

The search cites only equalities with a source spelling at that point; a fact
from an earlier `have` or a proof `if` condition inside a pure theorem has none
and is not offered. In a pure theorem, `ensures P by auto();` runs the same solver
and search around `simp`. `have name: P` also names the fact: until the end of
the enclosing block, `name` stands for `P` wherever a proposition is cited
whole, as in `using { name; }`, `rewrite(name)` or `contradiction(name)`, and is
read as `P` there, so citing it proves exactly what restating `P` proves.

The name is not visible inside the fact's own proof, and expansion writes `P` in
full
([`have_names_a_fact.md`](https://github.com/clicklang/click/blob/master/mdtests/have_names_a_fact.md)).

**Failure, checking, and tools:**

Any unfinished nested goal fails and adds nothing. A fact name that is already a
parameter, binding or fact name in scope is refused
([`have_name_refuses_a_name_in_scope.md`](https://github.com/clicklang/click/blob/master/mdtests/have_name_refuses_a_name_in_scope.md)).
Citing a name inside its fact's own proof or after its block ends is refused
with that reason
([`have_name_is_not_cited_in_its_own_proof.md`](https://github.com/clicklang/click/blob/master/mdtests/have_name_is_not_cited_in_its_own_proof.md),
[`have_name_is_cited_only_in_its_block.md`](https://github.com/clicklang/click/blob/master/mdtests/have_name_is_cited_only_in_its_block.md)).

A quantifier variable hides a fact of the same name in its body, and `intro() as
name` refuses a fact name in scope
([`intro_as_refuses_a_fact_name.md`](https://github.com/clicklang/click/blob/master/mdtests/intro_as_refuses_a_fact_name.md)).
The container stays intrinsically control; its selectable source site may own
simple work or expandable automation from its body.

**Checked examples:** [`post_execution_have_checks_each_path.md`](https://github.com/clicklang/click/blob/master/mdtests/post_execution_have_checks_each_path.md), [`have_names_a_fact.md`](https://github.com/clicklang/click/blob/master/mdtests/have_names_a_fact.md)

### Proposition branches

**Form:** `if P [ensuring { ... } then] { ... } else { ... }`

**Core.** Split pure reasoning into contexts containing `P` and `not P`, then
require both to prove the same goal. At an execution frontier, straight-line
arms that end at the same program point in the same state rejoin: the proof
continues once from that state, with the facts both arms established.

The arms may reason, run the same C statements, and unfold and refold resources.
The case facts and anything only one arm proved do not survive the join. With
`ensuring { fact ...; owns ...; views ...; } then`, the arms must rejoin through
that interface, as the arms of a `branch ensuring` do: both arms establish every
interface fact and hold every interface resource, and the proof continues once
from the state the interface describes, even when the arms ended in different
states.

`owns name: resource(...);` names an instance that carries fields: each arm
supplies the instance it has bound to `name`, the join gives `name` a fresh
model, and the interface's `fact` entries, checked against each arm's own model,
are all the proof knows about the fresh one. What follows the `if` is checked
once.

Without `ensuring`, two arms that are both still live and end in different
states or at different program points are refused when tactics follow the `if`
(`mdtests/proof_if_arms_must_rejoin.md`); when one arm reaches function exit,
those tactics belong to the other arm and run once, in it
(`mdtests/proof_if_one_arm_returns_and_the_other_continues.md`).

In a loop's `preserve` body the rule is the same, except that arms reaching
those tactics at different program points are different paths of the C and each
is finished its own way.

After execution the C state is fixed and each outcome path is finished on its
own. On a path where `P` is already decided, only the matching arm runs. When
`P` is open on some outcome path and tactics follow the `if`, the `if` is
refused, because its arms would not rejoin and what follows would be checked
once per arm (`mdtests/a_proof_if_after_execution_that_would_fork_is_refused.md`).
Write those tactics inside the arms instead
(`mdtests/a_proof_if_after_execution_closes_its_claims_in_each_arm.md`).

**Failure, checking, and tools:**

Either unfinished arm fails. Click checks both spelled branches; expansion
recurses into smart descendants, and profiling reports them.

**Checked examples:** [`proof_if_cases.md`](https://github.com/clicklang/click/blob/master/mdtests/proof_if_cases.md), [`proof_if_arms_rejoin.md`](https://github.com/clicklang/click/blob/master/mdtests/proof_if_arms_rejoin.md), [`proof_if_arms_rejoin_after_c_steps.md`](https://github.com/clicklang/click/blob/master/mdtests/proof_if_arms_rejoin_after_c_steps.md), [`proof_if_ensuring_rejoins.md`](https://github.com/clicklang/click/blob/master/mdtests/proof_if_ensuring_rejoins.md), [`proof_if_ensuring_named_resource.md`](https://github.com/clicklang/click/blob/master/mdtests/proof_if_ensuring_named_resource.md), [`proof_if_ensuring_named_resource_needs_fact.md`](https://github.com/clicklang/click/blob/master/mdtests/proof_if_ensuring_named_resource_needs_fact.md)

### Explicit cases

**Form:** `cases { A => { ... } B => { ... } }`

**Specialized.** Write it to use a disjunction that is already a fact, when its
arms are not `P` and `not P`; otherwise use `if`. Eliminate an exact available
disjunction: each arm receives exactly its own disjunct. Use `if P` to split on
a proposition you choose, which needs no premise because `P or not P` always
holds.

There is one arm per disjunct, any number from two, and the disjunction of the
arms grouped left to right as `or` parses (`A or B or C` is `(A or B) or C`)
must be available. Proving a focused proposition, every arm proves it. At an
execution frontier `cases` is a case split like a proof `if`, and follows the
same rule: with tactics written after it, its arms rejoin with the facts every
arm proved, or the `cases` is refused
(`mdtests/cases_arms_rejoin_with_the_facts_every_arm_proved.md`,
`mdtests/cases_arms_that_do_not_rejoin_are_refused.md`); an arm that reaches
function exit finishes its own path
(`mdtests/cases_at_a_frontier_finishes_each_arm.md`). In a loop's `preserve`
proof its arms must rejoin. After execution it splits each outcome path as a
proof `if` does: on a path whose facts decide a disjunct only that arm runs;
elsewhere the path forks into one path per arm, which needs the disjunction as an
exact fact on that path (`mdtests/cases_after_execution_splits_each_outcome_path.md`,
`mdtests/cases_after_execution_takes_the_decided_arm.md`), and tactics written
after a `cases` that forks are refused
(`mdtests/cases_after_execution_that_would_fork_is_refused.md`).

**Failure, checking, and tools:**

An unavailable disjunction or unfinished arm fails; this never substitutes `not
A` for `B` or implicitly branches C. Click checks both proof branches, expansion
recurses, and profiling reports descendants.

**Checked examples:** [`logical_tactics.rs`](https://github.com/clicklang/click/blob/master/src/surface/tests/tactic_tests/logical_tactics.rs), [`cases_in_have_before_and_after_execute.md`](https://github.com/clicklang/click/blob/master/mdtests/cases_in_have_before_and_after_execute.md), [`cases_at_a_frontier_finishes_each_arm.md`](https://github.com/clicklang/click/blob/master/mdtests/cases_at_a_frontier_finishes_each_arm.md), [`cases_arms_rejoin_with_the_facts_every_arm_proved.md`](https://github.com/clicklang/click/blob/master/mdtests/cases_arms_rejoin_with_the_facts_every_arm_proved.md), [`cases_at_a_frontier_requires_its_disjunction.md`](https://github.com/clicklang/click/blob/master/mdtests/cases_at_a_frontier_requires_its_disjunction.md), [`cases_after_execution_splits_each_outcome_path.md`](https://github.com/clicklang/click/blob/master/mdtests/cases_after_execution_splits_each_outcome_path.md), [`cases_after_execution_requires_its_disjunction.md`](https://github.com/clicklang/click/blob/master/mdtests/cases_after_execution_requires_its_disjunction.md)

### Scoped resource opening

**Form:** `open(resource) { ... }`

**Specialized.** Write it to work inside one layer of a composite resource and
have it folded back automatically at the end of the block. Temporarily replace a
held composite resource with one body layer, check the nested proof, then fold
it at scope exit. A model `match` inside the block uses the ordinary checked
constructor arms and joins: terminal arms each restore the resource at return;
an `ensuring` interface can rejoin before the block closes.

**Failure, checking, and tools:**

Missing ownership, an undecided guard, or failure to restore the body fails. A
body fact the closing fold leaves open is proved by the implicit `auto`, which
expansion prints as `open(...) { ... } by { ... }`. Click checks the exact
resource transition; expansion recurses, and profiling reports descendants.

**Checked examples:** [`resource_population_open.md`](https://github.com/clicklang/click/blob/master/mdtests/resource_population_open.md), [`open_scope_model_match_terminal.md`](https://github.com/clicklang/click/blob/master/mdtests/open_scope_model_match_terminal.md), [`open_scope_model_match_rejoins.md`](https://github.com/clicklang/click/blob/master/mdtests/open_scope_model_match_rejoins.md), [`open_scope_model_match_rejects_bad_arm.md`](https://github.com/clicklang/click/blob/master/mdtests/open_scope_model_match_rejects_bad_arm.md)

### Scoped resource opening with restoration

**Form:** `open(...) { ... } by { ... }`

**Expansion output.** `click expand` writes it; by hand, write it only to give
the close a different proof than the implicit `auto`. Closing an `open` scope
folds its resource again; the body after `by` proves the one body fact that fold
leaves open, as `fold(...) by { ... }` does, where the block ends, or after
execution when the block reaches function exit.

A bare `open` proves that fact by the implicit `auto`, which expansion prints as
this `by`. The body is one tactic call, such as `simp();`, or a block.

**Failure, checking, and tools:**

Refused when the close leaves no body fact open (superfluous) or more than one;
prove the others with `have` in the block. `open(...) { ... } by auto()` is a
syntax error: it means the bare `open`. Expansion keeps the `by` and prints the
body's checked steps; a smart tactic written in the `by` expands with its claim
(`click expand --claim`), not as a site of its own.

**Checked examples:** [`open_by_proves_the_closing_fold_body_fact.md`](https://github.com/clicklang/click/blob/master/mdtests/open_by_proves_the_closing_fold_body_fact.md), [`open_by_is_refused_when_the_close_leaves_nothing_open.md`](https://github.com/clicklang/click/blob/master/mdtests/open_by_is_refused_when_the_close_leaves_nothing_open.md)

### Existential witnesses

**Form:** `witness { name: value, ... };`

**Specialized.** Write it for an existential goal, naming the value that
satisfies it. On an existential goal, instantiate each named binder with its
value, in the order written, and continue with the instantiated body. One
`witness` can supply every binder of `exists (x: T, y: U) { ... }`.

**Failure, checking, and tools:**

A wrong binder, ill-typed value, or nonexistential goal fails. Click records the
exact witness; expansion is unchanged, and profiling charges one instantiation.

**Checked examples:** [`witness_and_choose.md`](https://github.com/clicklang/click/blob/master/mdtests/witness_and_choose.md)

### Obtaining witnesses

**Form:** `obtain (name: Type, ...) { P }`

**Specialized.** Write it to use an existential fact by naming its witness. Open
an already established `exists (name: Type, ...) { P }`, introducing the bound
values and instantiated body into the proof context. Each name is in scope for
every later tactic of the same proof block, whatever its type: a `have` goal, an
`instantiate` argument or `using` premise, a `contradiction` fact, a theorem
argument, or a `witness`.

**Failure, checking, and tools:**

An unavailable existential, wrong binder type, or name already in scope fails.
Prove the existential with `have` first if needed. Expansion retains this exact
step.

**Checked examples:** [`integer_exists_choose.md`](https://github.com/clicklang/click/blob/master/mdtests/integer_exists_choose.md)

## Exact integer product bounds

Inside `arithmetic_certificate rules`, the node
`integer_product_bounds bounds [i, j, k, l] => x * y <= T;` checks one
mathematical product bound. Its four references must name exactly available
premises `L <= x`, `x <= U`, `M <= y`, and `y <= N`, in that order. Each
endpoint and the result bound `T` must be a constant Integer, and each
interval must have its lower endpoint at most its upper endpoint.

The checker computes `L*M`, `L*N`, `U*M`, and `U*N` using exact integers.
For an upper bound, all four must be at most `T`; for the result `T <= x * y`,
all four must be at least `T`. The rule accepts negative, zero, and crossing
intervals and bounds weaker than the exact endpoints. It selects four facts
by index and does no premise search or implicit machine-range inference.

The result must contain an Integer multiplication at its root. Products
already reduced to a constant or a single operand, such as `x * 0` or `x * 1`,
use ordinary simplification instead. To relate machine values, multiply
separate observers, such as `to_integer(a) * to_integer(b)`. A bound on that
product does not establish the definedness of the machine operation `a * b`.
Native wide machine arithmetic needs its own checked width and conversion
rules. The [checked regression](https://github.com/clicklang/click/blob/master/mdtests/integer_product_bounds.md)
proves both signed 128-bit range endpoints for a signed 64-by-32-bit
mathematical product.

## Resources and snapshots

| Form | Class | Audience | Purpose | Details |
| --- | --- | --- | --- | --- |
| `transport(P, Q)` | smart | Specialized | Carry a fact from an earlier memory state. | [Reference](#fact-transport) |
| `transport(P, Q) using { R; ... }` | simple | Expansion output | Carry a fact using explicit frame evidence. | [Reference](#transport-with-selected-premises) |
| `unfold(name)` | simple | Core | Make a predicate transparent in the current proof branch. | [Reference](#unfolding-predicates) |
| `unfold(resource(args))` | simple | Core | Open an owned resource instance. | [Reference](#unfolding-resources) |
| `fold(resource)` | simple | Core | Assemble a resource from its body and children. | [Reference](#folding-resources) |
| `fold(...) by { ... }` | control | Expansion output | Supply a proof for one fold obligation. | [Reference](#folding-with-one-obligation) |
| `fold(...) { requires P by ...; }` | control | Expansion output | Supply proofs for selected fold obligations. | [Reference](#folding-with-several-obligations) |
| `construct(resource)` | simple | Specialized | Create an abstract token authorized by a `constructs` clause. | [Reference](#constructing-resources) |
| `take(base[a..b])` | simple | Specialized | Take one element out of iterated ownership. | [Reference](#taking-a-range) |
| `give(base[a..b])` | simple | Specialized | Return a taken element to iterated ownership. | [Reference](#giving-a-range) |
| `gather(resource(args))` | simple | Specialized | Form iterated ownership from its covering range. | [Reference](#gathering-resources) |
| `scatter(resource(args))` | simple | Specialized | Dissolve iterated ownership into its covering range. | [Reference](#scattering-resources) |
| `name(args, { binder: instance })` | simple | Specialized | Apply a verified tactic with resource bindings. | [Reference](#user-defined-tactic-calls) |
| `observe(resource)` | simple | Specialized | Read a resource's persistent observations. | [Reference](#observing-resources) |
| `close_invariants()` | smart | Core | Prove the invariant obligations at a loop back edge. | [Reference](#closing-loop-invariants) |
| `close_invariants() by` | control | Expansion output | Supply explicit proofs for invariant closure. | [Reference](#explicit-invariant-closure) |

Predicate calls are opaque to framing until their definitions are unfolded.
To carry such a fact across C execution, run `unfold(name)` before the relevant
steps and transport the unfolded definition.

### Fact transport

**Form:** `transport(P, Q)`

**Specialized.** Write it when a fact stated at an earlier state is needed at
the current one and neither `step` nor `simp` carried it. When exact source `P`
is available, derive target `Q` at another certified snapshot by selecting frame
evidence.

**Failure, checking, and tools:**

Unrelated propositions, unsafe writes, or a bounded evidence miss fail. When
no premise the planner selects carries the source, the refusal is the one the
same transport gets with its source listed in `using`: it names the effects
between the two states and, for a quantified fact, the leaf the frame could
not carry. Click checks the chosen transport; expansion adds `using`, and
profiling reports search and leaves.

**Checked examples:** [`simple_statement_step_explicit_transport.md`](https://github.com/clicklang/click/blob/master/mdtests/simple_statement_step_explicit_transport.md), [`transport_model_pointer_binding.md`](https://github.com/clicklang/click/blob/master/mdtests/transport_model_pointer_binding.md)

### Transport with selected premises

**Form:** `transport(P, Q) using { R; ... }`

**Expansion output.** `click expand` writes it; by hand, prefer the bare form,
which selects its frame evidence. Derive target proposition `Q` from exact
source `P` using only the listed snapshot and frame evidence. Available in a
pure theorem too, where the listed premises are all there is to read.

A `viewable` target is decided by the kernel's viewability rules, so a range
narrows to a sub-range the listed order facts place inside it, provided the
source range is established to be a valid 32-bit byte extent. A fact about an
application of an `Integer` range-fold function whose body the kernel checks
reads its one `T[]` argument, for a C integer `T` such as `int32` or `uint64`,
only at the fold's own index crosses each store and checked call write set that an exact order fact or stated `separate(...)`
places outside the application's `lo..hi` cells; the proved application equality
grants no C access.

The rule answers the same for every caller, so `simp`'s snapshot transport
reaches it too. A universal fact `forall (k: int32) { G implies F }` crosses the
same steps: `k` is renamed fresh, `G` is assumed, and each read of `F` and `G`
is carried when the recorded history shows its cell unchanged between its two
snapshots, read against the current context's own facts (for example `k < n`
excluding a store to `dst[n]`, `k != cur`
excluding a store to `visited[cur]`, or `0 <= k and k < n` with a contract
separation placing `left[k]` apart from it). A source `A and B` reaches a
target that is only `A` or only `B`: after
`memset(dst, 7, 4); dst[4] = 0;`, `memset`'s guarded postcondition carries to
`(0u64..4u64).all(|k| { dst[k] == 7 })`, and `simp` offers that source when the
goal is held at a recorded point only as one of its conjuncts.

The structural frame carries `defined(...)` leaves through the typed-read
transport rule, preserving initialization and lifetime evidence. Equal read
values alone do not justify carrying definedness across deallocation. See the
[checked disjoint-store regression](https://github.com/clicklang/click/blob/master/mdtests/guarded_definedness_survives_a_disjoint_store.md).

The structural frame includes 64-bit equality and preserves the read kind, all
eight bytes, and the other operand. A source that is a reflexive equality, under
binders and guards, needs no proof and no `using` entry. A listed quantified
premise may name its own binder: a call's postcondition held under the binder
its lowering chose is cited by a written form with another, as in `apply using`.
At a completed return outcome the source may name a held fact without being
listed, up to its binder's name in the same way. Mid-execution the source must
be listed; a refused source that is an available fact is named as one to list.

**Failure, checking, and tools:**

An absent source, mismatched target, or insufficient evidence fails. A refused
narrowing names the order fact it needs, as the two segments were written. A
refused fold frame names the step it could not place, or why the function has no
checked read summary; a refused quantified frame prints the leaf it had and the
leaf it wanted.

Click checks that transport only; expansion is unchanged, and profiling charges
the named evidence.

**Checked examples:** [`field_derived_precise_effect_after_metadata_write.md`](https://github.com/clicklang/click/blob/master/mdtests/field_derived_precise_effect_after_metadata_write.md), [`have_viewable_prefix_of_a_range.md`](https://github.com/clicklang/click/blob/master/mdtests/have_viewable_prefix_of_a_range.md), [`sweep_maintains_a_zero_unmarked_count.md`](https://github.com/clicklang/click/blob/master/mdtests/sweep_maintains_a_zero_unmarked_count.md), [`sweep_prefix_survives_its_endpoint_store_by_simp.md`](https://github.com/clicklang/click/blob/master/mdtests/sweep_prefix_survives_its_endpoint_store_by_simp.md), [`quantified_frame_carries_a_fact_past_the_excluded_store.md`](https://github.com/clicklang/click/blob/master/mdtests/quantified_frame_carries_a_fact_past_the_excluded_store.md), [`quantified_frame_preserves_uint64_equality.md`](https://github.com/clicklang/click/blob/master/mdtests/quantified_frame_preserves_uint64_equality.md), [`memcpy_then_terminator_keeps_copied_bytes.md`](https://github.com/clicklang/click/blob/master/mdtests/memcpy_then_terminator_keeps_copied_bytes.md), [`a_guarded_memset_value_claim_crosses_a_disjoint_store.md`](https://github.com/clicklang/click/blob/master/mdtests/a_guarded_memset_value_claim_crosses_a_disjoint_store.md)

### Unfolding predicates

**Form:** `unfold(name)`

**Core.** Make the predicate `name` transparent for the rest of this proof
branch. Every available fact that mentions it gains its one-layer body, the
current goal is rewritten the same way, and a later goal that mentions it is
read through its body too. The argument is the predicate's name, not one call:
every instance opens together, found through the per-predicate fact index.

**Failure, checking, and tools:**

An unknown predicate fails. An `unfold` inside a `have` ends with it: the
predicate is opaque again afterwards. Click opens exactly the named predicate
layer; expansion is unchanged, and profiling charges the produced proposition.

**Checked examples:** [`sorted_predicate.md`](https://github.com/clicklang/click/blob/master/mdtests/sorted_predicate.md)

### Unfolding resources

**Form:** `unfold(resource(args))`

**Core.** Replace the exact held composite resource with one supported body
layer. For an `authorized` family it destroys one member and requires that
family's owned `authority(...)`; `unfold(authority(R(..)))` retires a population
whose count is zero. `let { slot: name, ... } = unfold(resource)` names the
opened children and C-typed fields; it is the one binding form.

On a declared resource the slots are the body's `let ... where` witnesses, bound
to the values the body binds them to, so a later `fold` spells a body fact over
a witness with its name
([`unfold_names_a_witness_for_a_fold_body_fact.md`](https://github.com/clicklang/click/blob/master/mdtests/unfold_names_a_witness_for_a_fold_body_fact.md));
this form needs an execution frontier.

**Failure, checking, and tools:**

An unknown or absent resource, bodyless definition, or undecided guard fails. A
trailing `unfold(resource) as { ... }` map is refused with the `let` form to
write. Click opens exactly one resource layer; expansion is unchanged, and
profiling charges the produced body.

**Checked examples:** [`composite_resource_composes_token.md`](https://github.com/clicklang/click/blob/master/mdtests/composite_resource_composes_token.md), [`unfold_names_its_pieces_on_the_left.md`](https://github.com/clicklang/click/blob/master/mdtests/unfold_names_its_pieces_on_the_left.md)

### Folding resources

**Form:** `fold(resource)`

**Core.** Check the current pure body facts without searching the proof context,
consume the contained resource facts, and produce the named composite resource.
Pure facts remain available. Folding a definition whose body views memory makes
the head hold that borrow open until the head is unfolded or consumed.

For an `authorized` family it creates one member and requires that family's
owned `authority(...)`; `fold(authority(R(..)))` establishes an empty
population. `let name = fold(resource, { field: value }, { slot: child })`
constructs an instance with fields from the named children; a child whose owned
resource has the slot's own name may be left out of the map, and a map left
empty is left out.

An instance name a proof binds, by `let name = fold(...)`, `unfold` or a call,
names its instance only to the end of the block that holds it, like every other
proof binder. The resource itself stays in the proof state after the block. To
name it after the block, bind it before the block or name it in the contract:
arms that `let d = fold(...)` a contract's `produces d` fill that instance.

**Failure, checking, and tools:**

A body fact no fact states exactly is left open and proved by the implicit
`auto` as the fold's `by`, which expansion prints; one `auto` cannot prove
fails, naming it. Before that, the kernel's condition decision settles a body
fact that is a condition, as a step's fast path does.

A body fact over a witness the proof cannot name has no requirement spelling, so
the fold is refused at it; the fold never searches. A missing body member, false
body fact, or undecided guard fails. A slot is taken by name only for the arm
the model selects, only from an owned, folded resource of the slot's family, and
never from the fold's own result; otherwise the fold names the missing child.

Click folds exactly the named resource, completing the child map before the
kernel checks it; expansion keeps a bare fold unless the implicit `auto` proved
a body fact, and profiling charges its body.

**Checked examples:** [`composite_resource_composes_token.md`](https://github.com/clicklang/click/blob/master/mdtests/composite_resource_composes_token.md), [`a_fold_takes_children_by_name.md`](https://github.com/clicklang/click/blob/master/mdtests/a_fold_takes_children_by_name.md), [`a_fold_does_not_take_an_unfolded_child_by_name.md`](https://github.com/clicklang/click/blob/master/mdtests/a_fold_does_not_take_an_unfolded_child_by_name.md), [`a_fold_does_not_take_a_child_of_another_family_by_name.md`](https://github.com/clicklang/click/blob/master/mdtests/a_fold_does_not_take_a_child_of_another_family_by_name.md), [`fold_proves_an_unstated_body_fact_by_implicit_auto.md`](https://github.com/clicklang/click/blob/master/mdtests/fold_proves_an_unstated_body_fact_by_implicit_auto.md), [`a_block_bound_instance_name_ends_with_its_block.md`](https://github.com/clicklang/click/blob/master/mdtests/a_block_bound_instance_name_ends_with_its_block.md), [`an_instance_bound_before_a_block_is_named_inside_it.md`](https://github.com/clicklang/click/blob/master/mdtests/an_instance_bound_before_a_block_is_named_inside_it.md)

### Folding with one obligation

**Form:** `fold(...) by { ... }`

**Expansion output.** `click expand` writes it; by hand, write it only to give
an open body fact a different proof than the implicit `auto`. Any `fold` form
followed by the proof of the one body fact its fast path leaves open, written as
the resource's body fact over the fold's arguments and proved at the fold, as a
`have` would.

The body is one tactic call, such as `simp();`, or a block.

**Failure, checking, and tools:**

Refused when the fast path leaves no body fact open (superfluous) or more than
one; the second refusal spells each as a `requires` entry to copy. `fold(...) by
auto` is a syntax error: it means `fold(...)`. Expansion keeps the `by` and
prints the body's checked steps.

**Checked examples:** [`fold_by_proves_its_one_open_body_fact.md`](https://github.com/clicklang/click/blob/master/mdtests/fold_by_proves_its_one_open_body_fact.md), [`fold_by_with_no_open_body_fact_is_superfluous.md`](https://github.com/clicklang/click/blob/master/mdtests/fold_by_with_no_open_body_fact_is_superfluous.md)

### Folding with several obligations

**Form:** `fold(...) { requires P by ...; }`

**Expansion output.** `click expand` writes it; by hand, write it only to give
several open body facts their own proofs. Any `fold` form followed by one
`requires [label:] P by ...;` entry per body fact it proves. Each `P` states
exactly one body fact the fast path leaves open; one no entry writes goes to the
implicit `auto`.

**Failure, checking, and tools:**

An entry that states no open body fact, or repeats an earlier entry's, fails
where it is written and lists the open body facts. Expansion keeps each entry
and prints its body's checked steps.

**Checked examples:** [`fold_requires_proves_each_open_body_fact.md`](https://github.com/clicklang/click/blob/master/mdtests/fold_requires_proves_each_open_body_fact.md)

### Constructing resources

**Form:** `construct(resource)`

**Specialized.** Write it at a function outcome whose contract `constructs` an
abstract token. At a function outcome, create exactly one owned abstract token
named by an authorized `constructs` clause without consuming an input resource.

**Failure, checking, and tools:**

A non-token, composite, duplicate, unauthorized, or pre-execution construction
fails, as does construction of an `authorized` family, whose members only `fold`
creates. Click checks the exact zero-source resource transition in the kernel;
expansion preserves the checked step, and profiling charges one simple leaf.

**Checked examples:** [`contract_tests.rs`](https://github.com/clicklang/click/blob/master/src/surface/tests/contract_tests.rs)

### Taking a range

**Form:** `take(base[a..b])`

**Specialized.** Write it to use one element of an iterated ownership fact as
ordinary owned memory. Move one element out of the unfolded iterated ownership
fact whose elements live at `base`, as ordinary owned memory. The element's
index must be known in range, its guard known true, and the index not already
out; the fact then claims nothing at that index.

**Failure, checking, and tools:**

An unknown or false guard, an index that may already be out, or a range that is
not one element fails. The kernel re-derives the step from its input state when
the trace is checked; expansion prints it unchanged, and profiling charges one
guard cell and the fact's taken-out indices.

**Checked examples:** [`iterated_ownership_allocate_one.md`](https://github.com/clicklang/click/blob/master/mdtests/iterated_ownership_allocate_one.md)

### Giving a range

**Form:** `give(base[a..b])`

**Specialized.** Write it to return an element taken with `take`. Move a
taken-out element back into its iterated ownership fact. Its guard must be known
true.

**Failure, checking, and tools:**

A guard that is false or unknown, or an element that is not out, fails. Checked
and expanded like `take`.

**Checked examples:** [`iterated_ownership_release_one.md`](https://github.com/clicklang/click/blob/master/mdtests/iterated_ownership_release_one.md)

### Gathering resources

**Form:** `gather(resource(args))`

**Specialized.** Write it to form an iterated ownership fact from the range it
covers. Form the iterated ownership fact the named resource's clause denotes:
from the owned range its elements cover when a quantified fact says every guard
is true, or from nothing when every guard is false.

The guard cells must be owned.

**Failure, checking, and tools:**

Guards that are not all known one way fail. The kernel instantiates the
quantified guard fact once at an arbitrary index; the range is never enumerated.

**Checked examples:** [`iterated_ownership_gather_scatter.md`](https://github.com/clicklang/click/blob/master/mdtests/iterated_ownership_gather_scatter.md)

### Scattering resources

**Form:** `scatter(resource(args))`

**Specialized.** Write it to dissolve an iterated ownership fact back into its
range. The converse of `gather`: consume the named clause's iterated fact, with
nothing taken out, and return the covering range when every guard is true, or
nothing when every guard is false.

**Failure, checking, and tools:**

As for `gather`.

**Checked examples:** [`iterated_ownership_gather_scatter.md`](https://github.com/clicklang/click/blob/master/mdtests/iterated_ownership_gather_scatter.md)

### User-defined tactic calls

**Form:** `name(args, { binder: instance })`

**Specialized.** Write it to apply a `tactic` the project declares, such as a
resource reshaping lemma. Apply the user-defined tactic `name` at the current
execution frontier, before the function exits: bind each of its supplied
resource binders to an instance the proof holds, check its `requires` as
available facts, consume its consumed instances, produce its produced instances
under the names of a `let { binder: name }` pattern, and add its `ensures`.

No C runs and memory is unchanged, so every fact about a cell survives. The map
may be omitted when the tactic supplies no binder.

**Failure, checking, and tools:**

A missing requirement is refused by name, as are a map entry naming an unknown
binder or an instance of the wrong resource, and an application after function
exit. Click applies the tactic's certified contract once; expansion leaves it
unchanged, and profiling charges one application.

**Checked examples:** [`user_tactic_reshapes_owned_resources.md`](https://github.com/clicklang/click/blob/master/mdtests/user_tactic_reshapes_owned_resources.md)

### Observing resources

**Form:** `observe(resource)`

**Specialized.** Write it to read a folded resource's view and facts without
unfolding it. Keep a held composite folded while projecting its declared
non-consuming view and immediate facts.

**Failure, checking, and tools:**

An absent resource or unsupported projection fails; owned contained resource
facts never leak. Click performs one projection layer, expansion is unchanged,
and profiling charges that layer.

**Checked examples:** [`composite_resource_folded_nested_fact_projection.md`](https://github.com/clicklang/click/blob/master/mdtests/composite_resource_folded_nested_fact_projection.md)

### Closing loop invariants

**Form:** `close_invariants()`

**Core.** At a loop back edge, which is the body's end or a stepped `continue`,
plan a checked body for the exact invariant value and safety obligations, and
for the ranking obligations a `decreases` clause adds after them. A ranking
obligation is closed by one `arithmetic() using` step citing the loop's declared
invariants, its guard, the function's written preconditions, and the C branch
conditions this path took, and a tuple's pivot by `left`/`right`.

A member the planner misses is tried with one `normalize() using` over those
named premises, trimmed to the ones it needs, which closes an unsigned or 64-bit
bound from the guard
([`back_edge_closes_an_unsigned_bound_from_the_guard.md`](https://github.com/clicklang/click/blob/master/mdtests/back_edge_closes_an_unsigned_bound_from_the_guard.md)).

A `preserve` path whose tactics stop inside the body first runs the rest of it
as an omitted `preserve` would
([`preserve_runs_the_rest_of_the_body.md`](https://github.com/clicklang/click/blob/master/mdtests/preserve_runs_the_rest_of_the_body.md)).
`close_invariants() by auto()` is refused, naming these forms
([`close_invariants_by_auto_is_refused.md`](https://github.com/clicklang/click/blob/master/mdtests/close_invariants_by_auto_is_refused.md)).

**Failure, checking, and tools:**

A bounded planning miss fails locally, and a ranked loop's diagnostic names the
ranking obligations; one needing an inequality outside that named set fails
there rather than starting a search. Spell `close_invariants() by { ... }` with
explicit steps when needed. Expansion emits the retained body and never repeats
invariant discovery while checking it.

**Checked examples:** [`c_decreases_count_up.md`](https://github.com/clicklang/click/blob/master/mdtests/c_decreases_count_up.md)

### Explicit invariant closure

**Form:** `close_invariants() by`

**Expansion output.** `click expand` writes it; by hand, write it only when the
planned closer misses and the invariant bundle needs explicit steps. At a loop
back edge, check a nonempty `{ ... }` proof, or one tactic call written without
braces, of the exact lowered value and safety obligations, followed by one `0 <=
component` member per `decreases` component and one lexicographic decrease
member.

Use `both { ... } and { ... }` for conjuncts, and `left`/`right` to choose the
decrease pivot.

**Failure, checking, and tools:**

Missing, incomplete, premature, or repeated bodies fail without automatic
fallback. The body is retained by expansion; the container owns its source site.
Kernel bundle validation remains an independent check.

**Checked examples:** [`loop_invariant_body.md`](https://github.com/clicklang/click/blob/master/mdtests/loop_invariant_body.md)

## Expansion, profiling, and audit

`click expand` replaces a selected smart tactic with its checked explicit
proof. Expanded proofs use only canonical surface names; internal
Rust variants such as certified statement transitions are not a second user
vocabulary. Expansion starts from a correct selected proof unit and verifies
that complete proof unit again after rewriting it. It does not emit a partial
rewrite when a later tactic in the same proof is failing.

Expansion removes the selected tactic's avoidable planning and search cost; it
does not remove the unavoidable work of checking the emitted operations or
reading the longer explicit proof. A smart hotspot should therefore become
approximately as cheap as its direct checked proof permits. A materially slow
simple leaf is an engine defect rather than another expansion opportunity.

`click expand --claim LABEL` applies the same checked rewrite to every smart
tactic in one function claim. This avoids manual site-by-site work when the
aggregate search cost is significant even though each smart tactic is prompt.

`click profile` reports smart and simple work under the same concepts:
statement transitions are `step`, checked loop transitions are `loop`,
fact transports are `transport`, and atomic
reasoning uses rules such as `assumption`, `normalize`, `rewrite`, and named
theorem applications. A slow simple leaf is a Click performance bug. A
successful slow smart tactic is an expansion candidate. An unsuccessful smart
tactic has nothing to expand; decompose that proof unless its search failed to
respect its bound or expose an actionable next step.

`click audit` finds smart tactics in a project, expands each one, and verifies
the rewritten source. Its purpose is to detect missing or invalid expanded
proofs, not to promise constant total verification time as a project
grows.


## Arithmetic bridge prerequisites

`auto` carries connected machine comparisons into mathematical `Integer`
comparisons through checked standard-library theorems. When observing an
addition or subtraction requires its own definedness or no-wrap bound, a
nested search does not re-enter the same operation's bridge. Already available
prerequisites can still justify the observation; a cyclic attempt is a search
miss. No stack size or work budget is raised.

[UInt64 successor with an additional bound](https://github.com/clicklang/click/blob/master/mdtests/uint64_successor_auto_with_additional_bound.md)
checks that an extra machine bound does not make an arithmetic proof recurse
indefinitely. Its false-small-bound companion keeps an unprovable conversion
bound rejected.
