# User-defined tactics (design)

Status: delivery step 1 is implemented: declarations, certification of
non-recursive tactics, and application in C proofs before function exit (see
[User-defined tactics](../reference/language/index.md#user-defined-tactics)).
Recursion and the later steps are still proposals, so the recursive example
below is in a `text` fence.

## Why Click needs them

A proof moves ownership only one layer at a time, with `fold` and `unfold`.
That suffices whenever the number of layers is fixed by the proof's text. It
fails when the number is a symbolic quantity that the C does not walk. The
Linux insert fixup `__rb_insert` stops at an arbitrary depth, and its natural
contract hands back the whole tree at `root->rb_node`. Producing that means
one `fold` per context frame above the stopping point. No finite script writes
that many folds, and the C has no loop or recursion that climbs back up for a
proof to ride on. The erase design meets the same wall when it merges its
spine back into an ordinary context.

Facts about models already handle unbounded depth: pure theorems prove
`plug(ctx, sub)` red-black by `induct`. The gap is ownership. A user-defined
tactic closes it with recursion. Its contract is proved once, by induction on
a measure, where the recursive application is the induction hypothesis; each
later application is one checked step. Without recursion a user tactic only
abbreviates steps a proof could already write, which is a convenience; with
recursion it makes true contracts provable that are unprovable today.

## The idea

A tactic is a checked rule from one proof state to another. It consumes some
resource instances and facts and produces others. It changes the proof's
resource context and fact context, never memory and never C state.

```text
tactic refold_to_root(focus: struct rb_node*, root: struct rb_root*) {
    decreases c;
    consumes c: ctx_at(focus, root);
    consumes t: rb_at(focus);
    requires ctx_holds(c.model, t.model) == 1;
    produces tree: rb_at(root->rb_node);
    ensures tree.model == plug(old(c.model), old(t.model));
} by {
    match c.model {
        Context::Top => { ... the focus is root->rb_node; rename t ... },
        Context::Left(identity, grandparent, color, sibling_model, up_model) => {
            let { sibling: s, up: u } = unfold(c);
            let sub = fold(rb_at(identity), { ... }, { left: t, right: s });
            let { tree: whole } = refold_to_root(identity, root) { c: u, t: sub };
        },
        Context::Right(...) => { ... mirrored ... },
    }
}
```

A C proof applies it with an explicit binder map, like a call step but with no
C statement:

```text
let { tree: tr } = refold_to_root(node, root) { c: c, t: t };
```

## Declaration

- **Parameters.** Any Click type: C scalars and pointers, `Integer`, `Nat`,
  spec enums and models. A non-C parameter is a logical parameter, as a
  theorem's is; nothing about it is C storage.
- **Clauses.** The contract clauses of a function: `consumes`, `produces`,
  `owns` (held in and out), `views`, `requires`, `ensures`. `old(...)` reads
  the proof state before the application. `exceptional ensures` and
  `constructs` do not apply, since no code runs.
- **Termination is required.** `diverges` is refused. A non-recursive tactic
  terminates by construction, as a straight-line C function does. A recursive
  one must declare `decreases`: structural on a consumed or owned binder
  (`decreases c;`), an expression measure, or a lexicographic tuple. A
  non-terminating recursive tactic would make its own contract an unproved
  assumption and could prove false. In step 1 recursion cannot be written: a
  tactic's name becomes applicable only after its declaration, so a body can
  apply earlier tactics only.
- **Language neutrality.** Nothing in a declaration names a C construct
  beyond the pointer and scalar types the shared contract language already
  spells. A tactic may live in a theorem-only `.click` file and be imported by
  C, C++, and Rust sidecars alike: all three frontends lower to one execution
  IR and share the kernel, and a tactic is defined over that shared proof
  state.

## Proof body

The `by` block is an ordinary proof at a fixed execution point. It may use
`match`, `unfold`, `fold`, `have`, theorem application, applications of
tactics (itself included), `if`/`cases` on propositions, and smart tactics
such as `simp`. It may not use `step`, `execute`, `branch`, `loop`, or any
other tactic that advances C. The proof ends when every produced instance and
every `ensures` is established; there is no exit statement to step to.

A recursive application inside the body is the induction hypothesis. It owes
the measure's descent at that application:

- structural: the instance bound to the measured binder is a strict contained
  descendant of the tactic's own measured instance, reached through unfolds
  this path performed (the same evidence rule as structural loop measures);
- expression: the measure at the application is nonnegative and strictly
  smaller, as ordinary proof obligations.

Mutual recursion among tactics is ranked by the same rules over their
component, as for C functions.

## Application

- **Where.** Anywhere a proof has a current state: a C function proof before
  and after its exit, loop `initialize` and `preserve`, `branch` and proof
  `if` arms, other tactic bodies, and pure theorem proofs when the tactic has
  no resource clauses.
- **What it checks.** Every `requires`, and every consumed or owned binder
  bound to an instance the proof holds, of the declared resource type and
  arguments. Nothing is searched: the binder map and output pattern are the
  only bindings, as for call steps.
- **What it does.** Removes the consumed instances, adds the produced ones
  under the output names, adds the `ensures` facts. Memory is unchanged, and
  every fact the proof holds about cells remains valid.
- **Classification.** An application is a simple tactic. `click expand` never
  expands it, and `click audit` inventories the smart sites inside tactic
  bodies like those in any proof.

## Kernel

There is no new certification judgment, and one new checked proof event, the
application.

- **Certification.** A tactic is certified as the contract of a procedure in
  the shared kernel IR whose whole body is `return;`, with an empty write
  frame. A procedure that runs no code changes nothing but the resources its
  contract transfers, so its contract holds of a proof state exactly when the
  tactic's does. Certifying it reuses every existing check: the contract's
  entry state, resource transfer, recursion hypotheses, termination, rule
  packaging (`c_verified_function_rule`), and the audit's targeted runs. The
  surface proves it with the tactic's script followed by the one `return`
  step and one `assumption` per claim, so the script itself must leave each
  produced instance held and each `ensures` available. The IR is the one all
  three frontends lower to, so nothing about this is specific to C.
- **Termination.** Tactic rules join the termination check as their own call
  graph, with application edges instead of call edges. A tactic cannot apply a
  C function, so the graph is tactics only.
- **Application event.** `CheckedExecutionEvent::TacticApplication` records a
  tactic application at a frontier. The kernel builds it only through
  `apply_verified_tactic_rule`, which refuses any procedure whose body is not
  exactly `return;` and applies the procedure's verified rule (or, in a
  targeted run, its scoped assumption) through the ordinary call boundary,
  with the proof's binder map. Inserting a call to a procedure that runs no
  code changes nothing the program does, which is why the rule may be applied
  with no C statement. Every precondition must already be an available fact.
  The empty write frame is what leaves memory unchanged: the boundary havocs
  only the frame, and the frame was certified against the body. Trace
  certification connects the event's before and after states like any other
  resource event.

The trusted addition is the application event and its body check. All
reasoning inside a tactic body reuses existing checked steps.

## Delivery

One design, delivered in pull requests on it:

1. Declaration, parsing, validation, certification of a non-recursive tactic,
   and application in C proofs, with the event and no-havoc transfer. The
   tactic expand/audit inventory and every per-variant tactic table join here.
2. Recursion: self-recursion with structural and expression measures, the
   tactic call graph, and refusal of unranked recursion and `diverges`.
3. Cross-backend regressions: one imported tactic applied in a C proof, a C++
   proof, and a Rust proof, with a refusal in each.
4. Click-typed logical parameters (`Integer`, `Nat`, models), application in
   pure theorem proofs, mutual recursion, and lexicographic measures.
5. The consumer: `refold_to_root`, and `__rb_insert` restated to produce
   `rb_at(root->rb_node)`.

## Regressions owed

- Positive: a non-recursive tactic, a recursive structural refold over a
  context chain of unknown depth, an expression-ranked recursive tactic, and
  application before and after a function's exit and in a loop body.
- Refused: an application missing a `requires`; a binder bound to the wrong
  resource type or an instance not held; reuse of a consumed instance after
  the application; a recursive application whose measured instance is not a
  strict descendant; a tactic without `decreases`; a tactic declaring
  `diverges`; a `step` inside a tactic body.
- Memory: a fact about a cell outside the tactic's footprint, and one inside
  it, both survive an application unchanged.
- Scaling: certification work linear in the body; application work linear in
  the binder map and the `ensures`, independent of how deep the tactic's
  recursion is.

## Decisions

- Application is spelled like every other tactic, `name(args)`, with an
  optional binder map and output pattern:
  `let { tree: tr } = refold_to_root(node, root) { c: c, t: t };`. `apply` stays
  for applying theorems, which are not tactics. A tactic name may not shadow a
  built-in tactic.
- Delivery follows the order above: recursion before Click-typed logical
  parameters, since the rbtree consumer needs only C-typed parameters.
