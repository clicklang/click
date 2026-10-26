# Proof workflow

This page is the working loop for writing a Click proof: the proof kinds,
tactics, explicit proof scripts, loop proofs, and what to do when a proof does
not close. Click proofs live in `by` clauses.

When a proof does not close, first determine whether the claim is false, the
proof needs explicit supported steps, or Click has a language, correctness, or
tooling defect. The [proof-failure triage guide](proof-failure-triage.md)
gives the canonical classification and reduction workflow. In particular, a
prompt failure from an incomplete smart tactic is not by itself an engine bug.

## Proof kinds

A **pure proof** derives a proposition without a symbolic C state. This is the
context used for pure theorem proofs.

A **fixed-state proof** reasons against one fixed symbolic C state. It refines
propositions but does not advance C. The nested proof inside
`have ... by { ... }`, loop initialization, and result-aware outcome proofs are
fixed-state proofs. A `have` body or loop initialization cannot transform
resources; a result-aware outcome proof can fold and unfold logical resources.

An **execution proof** establishes a relationship between the entry and exit of
a code region. It owns an execution frontier consisting of the current program
point, symbolic C state, pure facts, resource facts, and pending control-flow
continuations. Execution steps move that frontier forward. Pure reasoning and
resource reasoning may occur between execution steps without moving it.

A function-contract proof is therefore an execution proof even when some of
its individual steps are non-executing. Loop initialization is a fixed-state
proof at the loop entry; loop preservation is an execution proof of one
arbitrary iteration.
Together they justify the loop rule used by the execution proof of the
enclosing function region.

For contracts with several claims, a trailing `by { ... }` block is one
grouped execution proof of the function contract:

<!-- verified-example: mdtests/grouped_function_proof.md -->
```click
int32 set_first(int32 p[], int32 value) {
    owns p[0..1];
    ensures result == value;
    ensures p[0] == value;
}
```

Click checks the C region once. Every postcondition is then checked against the
resulting shared proof state. A claim with its own `by` keeps that independent
proof, and the grouped proof covers the claims without one. When two or more
claims omit their proofs, they share one omitted grouped proof.

## The implicit tail

Every proof script ends with an implicit tail, and an omitted proof is that
tail alone. The tail runs the C that is left from where the script stopped,
checking declared loops as it reaches them. At each C branch the facts do not
decide, it splits into paths that each run to function exit. It then closes
every open goal on every path with the implicit closer, which tries direct
closure and then `solve`'s search. On a returned path that holds the body of a
resource the contract `produces`, the closer also folds that resource. Folds
of other resources and theorem applications stay written.

A script therefore needs no final closer and no step to function exit. A
script may stop after any statement, before a C branch included
(`mdtests/a_script_that_stops_with_c_left_is_finished.md`):

<!-- verified-example: mdtests/a_script_that_stops_with_c_left_is_finished.md -->
```click
int32 magnitude(int32 x) {
    requires x > -100 and x < 100;
    ensures result >= 0;
} by {
    step();
}
```

Here the script steps over `int32 y = 0;`, and the tail runs the C `if`, one
path per arm, and closes `result >= 0` on each. A script that ends in a split
whose arms each reach their own end, such as `match` or `outcomes`, ends in
those arms, and each arm has its own tail. The tail's execution and closing are
charged to the smart budget at the site after the script's last tactic.
`} by auto();` is the older spelling of the omitted proof, still accepted.

A proof is at one program point at a time. Once a script reaches function exit
on its path, with `step_until(function.exit)` or inside one arm of a proof
`if`, the tactics that follow act on that path. Its open goals are the
contract's claims in contract order, resource claims included. `fold`,
`apply`, and `have` transform the current path. A closer such as `solve()`,
`assumption()`, `normalize() using` or `solve() using` acts on the first open
goal, the last two from exactly their listed premises when the explicit closer
is preferable to search, and the implicit tail closes every goal still open.
A later fact or fold does not retroactively affect an earlier closing step.

## Tactics

A one-tactic proof needs no braces:

<!-- verified-example: mdtests/algebraic_maybe.md -->
```click
by solve();
```

`by solve();` means the same as `by { solve(); }`. `solve()` closes the first
open goal at the current frontier and runs no C; the implicit tail then runs
any C that is left and closes the rest. On a `have` or a pure theorem's
`ensures`, `by solve();` restates what the omitted proof does. On a C
function's `ensures` it is refused, because execution has not reached function
exit there; omit the proof instead. `simp()` and a written `auto();` are older
spellings of `solve()`, still accepted. See the
[proof tactics reference](../reference/tactics/index.md).

Expansion records the steps, splits and closers the implicit tail took, so an
expanded proof does not depend on proof search. The
[tactic reference](../reference/tactics/index.md#automation-and-search) gives
the order of the implicit closer's searches.

`solve` is the written smart tactic: a contextual simplifier. It is useful for
straight-line postconditions and unfolded predicate goals. It simplifies logical connectives,
constant/reflexive integer comparisons, small arithmetic forms, concrete folds,
and several kernel equality patterns. For order goals, it also rewrites through
known equalities, evaluates equality-linked constant arithmetic, and uses the
discrete relationship between strict and non-strict integer bounds.

The exhaustive simple/smart classification is in the
[proof tactics reference](../reference/tactics/index.md).

## Explicit proof scripts

Explicit proof scripts use function-call-shaped tactics:

<!-- verified-example: mdtests/step_until_steps_to_function_exit.md -->
```click
} by {
    step_until(function.exit);
    have result == x + 1;
}
```

`step_until(function.exit)` steps to function exit, where `result` names the
returned value, and the `have` proves a fact there; the implicit tail closes
the contract's claims.

Current tactics. The [proof tactics reference](../reference/tactics/index.md) is the
authoritative inventory and classifies each spelling as simple, smart, or
control flow. Its [core tactics](../reference/tactics/index.md#core-tactics)
are the fifteen or so a hand-written proof needs; the rest are specialized or
expansion output.

- `step()`: execute the next C statement with every fact in the proof
  context visible to the kernel. A fact about a cell the context proves the
  statement leaves untouched keeps that cell's name and stays true; a fact
  about a cell the statement may write is renamed. Use an explicit
  `transport(source, target)` when relating such a fact to the new state
  needs more reasoning than the context gives the step. At a C `if`, an
  available condition fact selects and enters one arm. At a loop head, it
  evaluates the condition once and enters one iteration or advances past the
  loop.
- `step_until(target)`: repeat `step()` up to a target. It walks a loop the
  facts decide and never splits: at a C branch the facts do not decide it is
  refused, and names the proof `if` or `branch` to write there. The targets
  are `statement(i)` and its chains such as `statement(i).statement(j)` and
  `statement(i).call(f, j)`, `region(N)`, `loop(N)`, `assignment(x, N)`,
  `read(N)`, `back_edge()`, `loop(i).back_edge()`, and `function.exit`. The
  target must be forward and reachable on the current execution path.
  `execute_until` is its older spelling, still accepted.
- `loop { ... }`: verify the loop exactly at the current frontier and advance
  to its checked abstract exit. Its nested `initialize`, `preserve`, invariant,
  invariant, and resource clauses construct the kernel rule; it never seeks to a
  numbered source loop.
- `close_invariants()`: discharge a loop's whole invariant bundle at the back
  edge. It is accepted only inside `preserve by { ... }`, and at most once per
  path. Omitting it makes Click append the closer implicitly.
- `unfold(name);`: make the predicate `name` transparent for the rest of the
  branch, in its facts, the current goal, and later goals.
- `unfold(resource);`: consume one owned composite resource fact and expose its
  immediate body facts.
- `fold(resource);`: require every declared pure body fact exactly, by
  context-free normalization, or by the kernel's condition decision (the one a
  step's fast path makes), consume one immediate composite body, and rebuild
  the owned composite resource fact. A body fact these miss is a requirement:
  prove it in `fold(resource) by { ... }` or
  `fold(resource) { requires P by ...; }`, or leave it to the implicit closer
  that proves a step's open requirements.
- `apply(theorem_name(args...));`: instantiate one verified pure theorem from
  the standard library or current file. It looks each requirement up among
  the current facts and proves none: a requirement it cannot find is a search
  miss, so state it first with `have P by { ... }`. It adds the theorem's
  conclusions and never changes the resource context. This bare spelling is
  smart because it searches for its premises.
- `apply(theorem_name(args...)) using { P; ... }`: the simple spelling,
  drawing premises only from the listed facts. Expansion rewrites bare `apply`
  into this form.
- `have proposition by { ... }`: run a scoped fixed-state proof and add its proposition
  to the current pure facts. The nested proof accepts
  `unfold`, `apply`, `obtain`, `witness`, `solve`, nested `have`, and proof-level
  `if` case analysis; it cannot execute C or transform resources. Both `if`
  branches prove the local proposition, after which the surrounding proof
  continues. At function exit, the `have` is proved on the current path, where
  `result` names that path's returned value.
- `if proposition { ... } else { ... }`: prove the current claim twice, once
  with the proposition added to the pure facts and once with its negation
  added. Each arm has its own proof script and its own path. Tactics written
  after the `if` run once, where the arms rejoin, so both arms must end at
  the same program point in the same state;
  `if P ensuring { ... } then { ... } else { ... }` states what they agree on
  when they do not. An arm that
  reaches function exit ends there instead, and the tactics after the `if`
  belong to the arm that continues. Placed before the C, a proof `if` tells
  apart paths that the C would split: each arm steps to exit with
  `step_until(function.exit)` and does its own exit work. It does not execute
  a C `if` statement.
- `observe(resource);`: project one view step from a held composite resource
  fact. This exposes immediate pure facts and viewed immediate contained
  resource facts without exposing owned contained resource facts.
- `obtain (k: int32) { P(k) }`: open the exact available existential
  `exists (k: int32) { P(k) }`, introducing `k` and its body as proof facts.
  Multiple typed bindings are allowed. The existential must already be
  established; use `have` first when it is not.
- `witness { k: expression };`: prove the current existential goal by substituting
  the given int32 expression for binder `k`.
- `assumption();`: close a goal already present as the same semantic fact; it
  does not normalize, extract, or transport a new fact.
- `normalize();`: close a pure goal by context-free computation.
- `rewrite(equality);`: rewrite the current proposition once using an exact
  available equality; the [tactic reference](../reference/tactics/index.md)
  lists the supported integer, pointer, and native unsigned forms.
- `transport(source, target);`: require an exact source fact and apply one
  certified atomic transport rule to establish the stated target fact at the
  current statement frontier. Conditions use framing; structural memory facts
  such as `viewable(...)` use the certified execution effects. Like `apply`,
  this bare spelling is smart.
- `transport(source, target) using { P; ... }`: the simple, exact-premise
  spelling of the same rule.
- `solve() using { Q; ... }`: smart simplification restricted to exactly the
  listed proposition facts. It tries arithmetic over them last, and a miss
  adds arithmetic's reason. `simp() using` and `arithmetic() using` are older
  spellings, and bare `arithmetic()` is the older spelling of
  `solve() using {}`. Expansion must produce named simple rules; if no
  explicit tactic vocabulary covers the selected proof, expansion fails
  locally instead of retaining a hidden search step.

- `intro();`, `contradiction(P);`: one
  structural logical rule each. `contradiction(P)` accepts either structural
  `not P` or the exact opposite polarity of the same lowered C condition. They are
  accepted only while a pure goal is active, typically inside `have ... by` or
  a theorem proof.
- `solve();`: close the first open goal by smart contextual simplification.
  It runs no C. `simp();` and a written `auto();` are older spellings.

An opaque predicate does not expose the memory footprint needed for framing.
When a predicate fact must cross execution, unfold it before those execution
steps and transport the unfolded definition; smart `transport` diagnoses this
case directly.

The implicit tail at the end of a per-claim `by { ... }` block closes that
claim. The tail of a trailing grouped function block closes every effect and
postcondition in the contract.

When the execution frontier is a C `if`, use `branch`:

<!-- verified-example: mdtests/step_proof_case_condition.md -->
```click
branch {
    step(); // Execute the first statement in the C then arm.
} else {
    step(); // Execute the first statement in the C else arm.
}
```

`branch` reads and consumes the C guard at the frontier. Ordinary `step()`
calls handle statements inside each arm. The arm states join at the shared C
continuation, and the following proof runs once. A nested C `if` uses another
`branch` when it reaches the frontier.

At every linear execution frontier there is exactly one current proof state.
The arm states created by `branch` are temporary subproofs, not persistent
path-sensitive continuations. Completed arms that return are retained only as
function outcomes; later tactics do not execute in them.

Add `ensuring` when branch-local execution should establish a common interface
before the rest of the function proof:

<!-- verified-example: mdtests/proof_branch_memory_continuation.md -->
```click
branch ensuring {
    fact p[0] >= 0;
    fact p[0] < 2147483647;
    owns p[0..1];
} then {
    step();
} else {
    step();
}
step();
```

`region(N).entry` means immediately before statement region `N` executes.
`region(N).exit` means immediately after it completes. Lowering assigns
statement IDs globally in source preorder: a compound statement receives its
ID before the statements nested in its arms or body. A sequence itself does
not receive an ID. Structural assertion and loop checks inserted by Click are
not source statements and do not consume IDs. Structural traversal, tactic
execution, snapshots, and expansion all use this same layout. Every
continuing arm must establish every `ensuring` assertion. Exact common facts
and resources remain available automatically; facts about changed state that
the continuation needs must be listed explicitly. Deterministic consequences
of listed resources, such as memory viewability and the read authority an owner
supports, remain available.

Arm-only snapshots are not exported. The function-entry state used by
`old(...)` and the common-frontier snapshot remain available. Changed
pointer-valued locals become fresh symbolic pointers at the join. The
interface must export the facts and resources needed to use them, such as
`views selected[0..len]`; symbolic pointers do not imply non-aliasing with
concrete allocations.

For example, pure case analysis needs no C execution:

<!-- verified-example: mdtests/proof_if_cases.md -->
```click
theorem int32_sign_split(x: int32) {
    ensures x <= 0 or x > 0 by {
        if x <= 0 {
            simp();
        } else {
            simp();
        }
    }
}
```

`unfold(predicate)`, `apply(theorem)`, `have`, and `fold(resource)` update the
current proof context immediately. They can therefore prepare the exact pure
fact or resource fact required by the following `step()` or `fold(resource)`.
Applications after function exit remain path-local, so `result` and post-state
expressions are interpreted separately for each completed path.

A successful implicit tail retains surface-expressible transition provenance
when the current tactic language can express the argument. Expansion can
render that provenance as an explicit proof.

An execution proof tracks an execution frontier: the current program point,
symbolic state, and enclosing continuation stack. Proof scripts can start at
function entry, advance by one statement with `step();`, unpack a C `if` at the
current frontier with `branch`, replace scoped paths with an explicit abstract
interface using `branch ensuring`, pause at a statement entry with
`step_until(region(N));`, and step to function exit with
`step_until(function.exit);`. The implicit tail runs whatever C the script
leaves.
Resource steps such as `observe`, `unfold`, and `fold` can happen between those
execution steps.

The execution frontier carries the same global statement ID assigned by
lowering. The source layout uses that ID to identify branch children,
continuations, and nested loops. Checks inserted by annotation lowering remain
attached to their source statement and do not become extra tactics.

Ordinary statement steps and frontier-local `branch` use the same certified
condition and statement transitions. A plain `branch` requires the continuing
arms to reach the same state. `branch ensuring` checks each listed fact and
resource independently in both concrete arms, then publishes one checked
abstract successor. A condition with only one kernel-feasible arm selects that
concrete path rather than merging it, while a terminal branch retains separate
return paths: each arm that returns is its own path, and its proof ends in
that arm.

A statement or condition can also have several checked paths that only their
facts tell apart: a load that may read the cell an earlier store wrote has one
successor where the addresses are equal and one where they differ, and
`x > 0 && y > 0` is false along two paths. `step()` and `branch` never split
the proof on such cases. They refuse at that statement, list the condition
each case assumes, and name the proof `if` that separates them; inside each
arm of that `if` the statement has one successor. The implicit tail makes the
same split itself, one condition at a time before the statement, and runs each
case to function exit as its own path. Its expansion prints the split as
nested proof `if`s.

A resource listed by `branch ensuring` remains in the representation named by
the interface. In particular, exporting a folded composite does not project
its declared body, containment facts, or child views. Use an explicit
`observe(composite(...))` after the join when the continuation needs that
one-layer projection.

At function entry, `views composite(...)` resource requirements are projected
one step automatically, matching `observe(composite(...))` for immediate
contained views. Owned composite resources still require an explicit
`observe(...)` when a proof wants to read through the folded resource.

Existential tactics are deterministic simple tactics, not search tactics. A
typical existential-introduction proof names a witness:

<!-- verified-example: mdtests/witness_and_choose.md -->
```click
ensures found_zero: (0..n).any(|k| { k == result }) by {
    step_until(function.exit);
    witness { k: 0 };
    solve();
}
```

`obtain` eliminates an already available existential. It names the
bound values and states the body of the existential; it does not select a
contract clause by name or position, and it does not prove the existential.

<!-- verified-example: mdtests/integer_exists_choose.md -->
```click
requires exists (x: Integer, y: Integer) { x == y };
ensures exists (a: Integer, b: Integer) { a == b } by {
    obtain (left: Integer, right: Integer) { left == right }
    witness { a: left };
    witness { b: right };
    assumption();
}
```

For a predicate requirement that hides an existential, unfold the predicate
first:

<!-- verified-example: mdtests/byte_slice_range_predicates.md -->
```click
requires bytes::contains(p, 0, (uint64) n, 'x');
ensures opened_contains: bytes::contains(p, 0, (uint64) n, 'x') by {
    step_until(function.exit);
    unfold(bytes::contains);
    obtain (found: uint64) {
        0u64 <= found and found < (uint64) n and p[found] == 'x'
    }
    witness { k: found };
    solve();
}
```

## Frontier facts and loop proofs

Use `have` to prove an intermediate proposition at the current execution
frontier. Loop proofs likewise operate where the frontier encounters a loop:

<!-- verified-example: mdtests/frontier_have_execute_until_and_mark.md -->
```click
by {
    step();
    step();
    have i == 0 by {
        solve();
    }
    loop as fill {
        decreases n - i;
        owns p[0..n];
        invariant i >= 0;
        invariant i <= n;
    }
}
```

`have` does not re-execute the function prefix. It sees the exact facts and
resources established by preceding `step()`, `unfold`, `fold`, and other
ordinary proof tactics. It proves its proposition on the current path and
adds the resulting fact to the following context.

`step_until(assignment(local, N))` selects the zero-based static occurrence
of an ordinary local assignment, local compound update, or call-result assignment in the executable
layout. It pauses before that store. Declarations and stores to other locals
do not count, so unrelated compiler temporaries do not shift the selection.
Occurrences follow structural preorder, including branch arms and loop bodies;
repeated loop iterations reuse the same static occurrence. The selector does
not execute an unreachable arm or move backward. A frontend may evaluate a
right-hand side in earlier helper statements: selecting the final local store
does not move the frontier before those helpers. Use `loop(N)` to stop before
a loop's header/body work and `mark` to name a reached state. Assignment
selectors currently serve `step_until`, not `at(...)` snapshot expressions.

`step_until(read(N))` stops before the zero-based Nth statement containing
an explicit scalar memory load, in executable preorder. A statement counts
once even when its expression contains several loads; repeated iterations
reuse the same static occurrence. This selects the whole statement, so a
conditional expression need not read on every path. Taking an address such as
`&*p` does not count as reading the pointed-to cell; a nested pointer load in
`&**pp` does count. Implicit aggregate copies and reads inside callees do not
count. The selector grants no access permission: `step()` checks the actual
operation using the current resources. Like assignment selectors, read
selectors serve execution targets rather than snapshot expressions.

`region(N)` selects the Nth source statement code region in structural
order for execution targets and snapshots:

<!-- verified-example: mdtests/frontier_have_execute_until_and_mark.md -->
```click
step_until(region(4));
have y >= 0 by {
    solve();
}
step();
have at(region(4).entry, y) >= 0 by {
    assumption();
}
```

`loop as name { ... }` creates entry and exit snapshot names for the loop at
the current frontier; the name is not a selector and never moves the frontier.

A code region is a static source construct with extent, such as a function,
loop, statement, or block. A program point is a proof-relevant boundary or
position in the program, often associated with a code region, such as
`loop_name.entry`. A visit is one runtime arrival at a program point. Visits
are useful semantic language, but they are not currently Click syntax.

Snapshot expressions use snapshot selectors. A selector can be a C program
point or a proof-local mark; the selected snapshot is the immutable state
recorded there:

```text
at(function.entry, x)
at(loop_name.entry, x)
at(region(0).entry, x)
at(region(0).exit, x)
at(region(0).entry, p[0] == 7)
at(region(0).entry, viewable(p[0..n]))
```

When a proof needs to remember the state it has already reached, prefer a
semantic proof-local name over repeating a numeric statement coordinate:

<!-- verified-example: mdtests/frontier_have_execute_until_and_mark.md -->
```click
mark before_write;
step();
have p[0] == at(before_write, p[0]) + 1 by solve();
```

The mark names the current state only. It does not advance or rewind the
frontier and cannot be passed to `step_until`.

`loop_name.entry` is available in invariants on that loop and in its explicit
`preserve` proof. Once the loop tactic succeeds, `loop_name.exit` is available
to the enclosing proof.

Statement entry and exit snapshots are currently recorded by deterministic
proof execution. `step()`, `step_until(...)`, and the implicit tail
record each deterministic boundary they cross. An `at(...)` expression reads
memory, reassigned parameters, and declared scalar, pointer, or array locals
from the selected state. `at(selector, proposition)` instead snapshots the
complete proposition; use this form for state-relative facts such as
`viewable(...)`, where snapshotting only the segment expression would leave the
memory component at the current state. Branch entries can have a unique
snapshot. An explicit loop `preserve` proof binds
`at(loop_name.entry, ...)` to its fresh arbitrary iteration state. Executing a
verified loop records its unique abstract exit as `at(loop_name.exit, ...)`.
Historical iteration visits still require a future selection model.

`invariant` declarations generate obligations at loop program points. The
loop-level `initialize` proof establishes the complete invariant set before the
first iteration. The `preserve` proof assumes that set and the loop condition,
executes one body iteration, and reestablishes the set:

<!-- verified-example: mdtests/count_to_loop_initialize_by_auto_and_preserve.md -->
```click
loop {
    decreases n - i;
    invariant i >= 0;
    invariant i <= n;

    preserve by {
        step();
        solve();
    }
}
```

Either phase may be omitted, as `initialize` is here. Bounded automation
attributed to the `loop` keyword supplies an omitted phase. An explicit preservation proof
runs in a fresh arbitrary-iteration context and must reach the loop back edge
on every proof branch. It can use ordinary tactics, including `have`,
resource operations, proof-level `if`, and branch execution.

An explicit initialization proof is an ordinary pure proof at the actual loop
entry. It can use `apply`, nested `have`, proof-level `if`, `unfold`, and `solve`,
but it cannot execute C or transform resources. A named loop's entry snapshot
is bound while this proof runs. The facts it proves are checked against the
kernel invariant instances before rule construction.

Execution-proof traversal advances forward through the function. When it
encounters a loop, it checks initialization at the current frontier, checks
preservation in a scoped arbitrary-iteration frontier, and advances the
enclosing execution proof with the loop's abstract exit rule. Later and nested
loops are therefore checked in their actual enclosing proof context; Click does not
reconstruct their entry states by executing the function prefix again.

Explicit `initialize` and `preserve` proofs directly supply the two premises for
that abstract exit rule. After initialization establishes every entry invariant
and every preservation branch reaches the back edge with the invariants and
effects reestablished, the kernel constructs the loop exit without proving
either premise again.

That abstract exit is justified by an opaque kernel `CVerifiedLoopRule` over the
symbolic loop-entry state and its required assumptions. The `loop` tactic
applies it immediately and advances the enclosing frontier. There is no later
summary tactic and no detached traversal from function entry.

## Loop frames

A loop frames by ownership. With no clause of its own it may write exactly the
memory the function owns, and it can narrow that authority the way a callee
contract does:

<!-- verified-example: mdtests/loop_owns_preserves_symbolic_index.md -->
```click
loop {
    owns p[0..n];
    invariant i >= 0;
}
```

A loop's owned segments must use stable names such as parameters or fields
reached through a stable owner, such as `owner->data[0..owner->len]`.
Structural loop setup projects the immediate core of a held composite resource,
so an owned `vector(owner)` can justify reading those fields without redundant
`views` clauses. A body store outside the loop's owned ranges is rejected at
the store, and a cell outside them holds its entry value after the loop with no
invariant.

The resulting frame is reusable. For example, if a loop owns only `dst[0..n]`
and requirements prove `separate(memory(dst[0..n]), memory(src[0..n]))`, an
omitted proof can prove source-memory postconditions without a handwritten source-invariance
invariant.

## Debugging failed proofs

Repair a failed proof by the [tracing procedure](tracing.md): find its goal,
then prove that goal through explicit intermediate `have` goals.

Failure messages usually include:

- guarantee label
- execution path index
- pure facts
- resource facts, when the failing tactic has a current resource context
- remaining proof obligations
- the goal a failed `solve` could not establish, in source spelling

Practical approach:

1. Find the failing mdtest and the exact guarantee label.
2. Read pure facts to learn which branch/path failed.
3. If a predicate is still opaque, add `unfold(predicate_name);`.
4. If memory preservation is missing, check `viewable`, `separate(memory(...))`,
   the contract's `owns`/`views` clauses, and the loop's owned resources.
5. If arithmetic overflow appears, add numeric requirements or invariants.
6. If the proof needs a general new pattern, add a focused mdtest and then a
   deterministic kernel/proof rule.
