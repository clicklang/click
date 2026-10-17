# Proof reuse and case structure

Design for [design-review](../issues/design-review.md) item P5 ("copy-paste
across case files and sidecars"). It measures where the repetition in
`examples/rbtree-erase` comes from, compares that with what Dafny, Verus,
Lean and separation-logic tools do, and lists what Click needs. It assumes
[SMT-backed `auto`](smt-auto-stage1.md) lands; it has. Measurements are from master at
`101ad5c7`.

## Summary

Most of the repetition is not a missing language feature:

- **Superseded increments.** Three quarters of rbtree-erase is development
  increments that a general proof has already superseded.
- **Mirror arms.** About half of the general color-repair proof is the
  left/right mirror of the other half.

Dafny and Verus have no symmetry feature. Their mirror arms are short because
each step is automatic, so the duplication costs little. Lean and Coq also
have automation, and in addition one tactic script can close several goals.

Click lacks four things:

1. automatic unfolding of recursive specification functions;
2. automatic folding and unfolding of resources;
3. one proof script reused across goals;
4. the habit, and the tooling, of keeping one general contract per function.

## Measurements

### Superseded increments

`rbtree-erase` has 41 sidecars and 39,582 lines.
`rbtree_erase_color_flips_red_all.click` (4,236 lines) proves the unchanged
`____rb_erase_color` under its general precondition: a one-black-level
deficit context with consistent parents. It has no case selector; a coverage
theorem derives the case split from the deficit invariant.

Twenty-two older color-repair sidecars each prove one case or a union of a
few cases. Every one of them is subsumed by that general proof. Together they
are **29,160 lines, 74% of the example**. They remain because mutation tests
point at them: 82 references in `tests/`, against 2 for the general proof.

The critique's "`__rb_change_child` contract copied into 24 files" is also in
these increments. Each one re-proves the helper inline because it predates
`rbtree_change_child.click`. The current proofs import that file, so contract
import works and is not a gap.

### Per-case contracts for `rb_erase`

`rb_erase` is verified in 11 sidecars, each under a case-selecting contract.
For example, `rbtree_erase_black_successor_wrapper.click` requires a black
root whose right child is a black leaf. No general `rb_erase` contract exists
yet; the rbtree issue lists wrapper integration as remaining work.

The language can already express one. A proof `match` whose arms each run to
function exit is supported (`docs/concepts/proof-scripts.md`). Conditional
resources can give a contract ownership that depends on the outcome: for
`__rb_erase_augmented`, either a balanced root and a null fixup parent, or a
deficit context and the parent to repair. This has not been tried yet.

### Mirror arms in the general proof

The loop's `preserve` proof matches on the context. The `Context::Right` arm
is 1,377 lines and the `Context::Left` arm is 1,385. After swapping
`Left`/`Right` and `left`/`right`, all but about 370 lines of each arm are
identical. Most of the remaining differences come from two sources:

- **Constructor argument order.** The child arguments of
  `RbTree::Node(id, parent, color, left, right)` must also be swapped, which
  a textual swap misses.
- **Comments.**

A few `step()`s really differ, because the Linux C is not symmetric: the two
arms read the sibling at different points. The theorem
section is also written in left/right pairs.

### What one arm is made of

The 1,377 lines of the `Context::Right` arm:

| Kind | Lines | Example |
|---|---|---|
| `have` | 617 | |
| … of which one rewrite then `assumption`/`normalize` | 222 | `have sm == Node(...) by { rewrite(sm == ...); normalize(); }` |
| unfolds of recursive spec functions | about 70 | `color_bit`, `rb_reparent`, `plug`, `rb_tree_parent_consistent` |
| resource `fold`/`unfold` | about 100 | `fold(rb_at(...))` 36, `ctx_at` 11, `rb_child_links` 22 |
| `step` | 106 | |
| `let` | 79 | |
| `fact`, `mark` | 74 | |
| `apply` | 61 | |

Many `have` lines restate a whole model term after a pointer update, and
some of those run to over 1,000 characters.

## What other systems have

| Technique | Dafny | Verus | Viper / VeriFast | Lean / Coq / Isabelle | Click |
|---|---|---|---|---|---|
| One verification condition covers every path; no per-step script | yes | yes | yes | no | no; each arm is scripted |
| Congruence and linear arithmetic per step | SMT | SMT | SMT | `simp`, `omega` | `auto` ([smt-auto-stage1.md](smt-auto-stage1.md)) |
| Recursive spec functions unfold automatically | fuel, default 1–2 levels | fuel | heuristics | `simp [f]` equation lemmas | explicit `unfold` |
| Heap facts carry across steps (framing) | `modifies`/`reads` | ownership types | permissions | n/a | partly; facts restated |
| Data-structure predicates open and close themselves | n/a, no separation logic | ownership types | Viper explicit; VeriFast auto-open/close | n/a | explicit `fold`/`unfold` |
| One script closes several goals | no | no | no | `<;>`, `all_goals`, Ltac, Lean macros | no; user tactics run no C |
| Symmetry (`wlog`, mirroring) | no | no | no | `wlog`, sometimes | no |
| Several contracts for one function, combined | no | no | VST: specification intersection | any number of theorems | one contract per sidecar |
| Contract import | modules | modules | yes | yes | yes |

## Needs

These are in order of value per unit of work. Each one stands on its own.

### R1. Retire superseded increments (process)

When a general proof subsumes an increment, delete the increment and point
its mutation checks at the general proof. The same applies to the `rb_erase`
case wrappers once a general contract lands. For rbtree-erase this removes
about 29,000 of 39,600 lines with no verifier change.

Cost: mutation checks against the 4,236-line proof are slower than against a
200-line case file. Measure them, and move them to nightly if they exceed the
gate budget.

Add a rule to `docs/internals/testing.md` or the examples guide: an example
keeps only its general proof and that proof's regressions.

Done: the 22 increments are deleted. Their 80 nightly mutation tests named 39
distinct C mutations; two were already checked against the general proof and
the other 37 now are. `examples/rbtree-erase` went from 44 sidecars and 39,582
lines to 22 sidecars and 10,422 lines. The gate is unaffected: the example and
all of these mutation tests were already nightly. The rule is in
`examples/README.md`.

### R2. One general contract per function

The norm is one contract per function. Cases become `match` arms inside one
proof, so the shared C prefix is executed once.

Prototype a general `__rb_erase_augmented` contract with an outcome-dependent
conditional resource, and a general `rb_erase` on top of it. If that works,
no feature is needed.

Not proposed: VST-style contract intersection, in which separate case
contracts are combined by a checked coverage obligation. It would keep
per-case development but re-execute the shared prefix once per case.
Reconsider it only if R2's prototype shows the single-proof form failing on
size or speed.

Done (2026-10-14): both general contracts landed in `examples/rbtree-erase`
and replaced 16 per-case sidecars. The prototype first verified only with
every exit's bookkeeping moved before the final C call, because return
certification refused a theorem applied after return. That bug and a
four-byte loadability fact over an eight-byte pointer store, which blocked
the same spelling, are fixed, so each exit now folds its outcome after the C
returns.

The general `__rb_erase_augmented` consumes `rb_at(node)` and
`ctx_at(node, root)`. It requires a nonempty node with `is_rb`, `ctx_rb` at the
node's black height and color, and `ctx_consistent`. It produces the node's
three fields and an outcome resource:

```click
spec enum EraseOutcome { Balanced(RbTree), Deficit(Context) }

resource erase_out(root: struct rb_root*, rebalance: struct rb_node*) {
    field model: EraseOutcome;
    match model {
        EraseOutcome::Balanced(t) => {
            owns whole: rb_root_at(root);
            fact whole.model == t;
            fact rebalance == 0;
        },
        EraseOutcome::Deficit(c) => {
            owns deficit: ctx_at(0, root);
            fact deficit.model == c;
            fact rebalance != 0;
            fact c != Context::Top;
            fact ctx_node_is(c, rebalance) == 1;
        },
    }
}
```

Its ensures are as follows:

- `out.model == erase_outcome(old(tree.model), old(up.model))`;
- `erase_out_rb(out.model) == 1`, meaning a red-black root, or a context
  missing one black level;
- parent consistency of `erase_out_tree(out.model)`;
- `erase_out_tree(out.model) == plug(old(up.model), erase_splice(old(tree.model)))`;
- the in-order sequence of `erase_splice` is the old left subtree's followed
  by the old right subtree's.

`erase_outcome` and `erase_splice` follow the C's decision sequence and reuse
the case files' model functions. Resource bodies cannot use recursive
functions, so validity is stated in ensures rather than as facts in
`erase_out`. The general `rb_erase` has the same requires. It produces
`rb_root_at(root)` whose model is `erase_outcome` repaired by
`erase_flips_red_all_result`, with validity, parent consistency, and the same
in-order statement. Its proof matches on `out.model` and calls
`____rb_erase_color` only in the `Deficit` arm.

The unlink proof has one arm per C exit. The arms are the leaf (black root,
black nonroot, and red), the left-only and right-only child, the immediate
successor (red leaf, black leaf, or child), and the deeper successor (black
leaf, or not). Two changes make the arms position-general:

- Arms step the verified `__rb_change_child` contract instead of executing it
  inline. This removes the case files' `Top`/`Left`/`Right` context split, so
  the three root-only immediate-successor proofs are subsumed by the nonroot
  ones.
- The deeper-successor arm is selected first, by an `if` on the tree shape.
  Its proofs reuse the spine files' bodies, which match the tree themselves.
  Under an outer constructor match the two binder sets for one subtree were
  not linked, and the inner fold of `rb_at(iid)` failed.

| | Sidecars | Lines | Verification |
|---|---|---|---|
| Before: the retired per-case sidecars | 16 | 4,815 | 37.7 s |
| After: general unlink, general `rb_erase`, shared refold tactic | 3 | 2,793 | 21.1 s |

The time is the sum of single release runs, one sidecar at a time. The
general unlink is 2,607 lines and takes 19.2 s as one proof unit; the general
`rb_erase` is 92 lines and takes 1.2 s. `refold_to_root` (94 lines, 0.7 s)
moved out of the color-repair proof into `rbtree_refold_to_root.click`, which
both proofs import. The single-proof form therefore does not fail on size or
speed, and contract intersection is not needed. `examples/rbtree-erase` went
from 22 sidecars and 9,747 lines to 9 sidecars and 7,504 lines.

`rbtree_erase_leaf_wrapper.click` stays: `examples/rbtree-augmented` imports
its leaf unlink, whose hole-and-context outputs that proof consumes. The
retired sidecars' 42 mutation tests named 25 distinct mutations of
`rb_erase_augmented.c`, and 14 more mutated the inlined `__rb_change_child`,
which the general unlink steps by contract and `rbtree_change_child.click`'s
own checks cover. The 25 are nightly checks against the general unlink, each
asserting the specific refusal. A mutation that deleted a statement is now a
same-length replacement: statement positions are counted in source preorder
(design-review W1), and a deletion would otherwise shift a later
`execute_until` and be refused for that instead. Two of them ran in the gate
against `rbtree_erase.click` in about 1 s each; against the general unlink
they take 13 to 14 s, so they are nightly too. The pinned-source checks stay
in the gate.

Other friction:

- Fields written before the `__rb_change_child` call needed
  `normalize() using { successor == er_id; }` to carry across it, or the
  subtree had to stay folded across the call.
- Two `by auto` steps in the merged proof exhausted their work budgets, after
  2 to 2.5 million units. One was a deeper-successor `ctx_node_is` disequality
  that passes in the retired `rbtree_erase_black_spine.click`; the other
  unfolded `erase_outcome`. Both were replaced by explicit steps. This is an
  observation; it has not been reduced.
- Unfolding an instance that `__rb_change_child` produced was refused after
  the C returned. The reduced post-return forms now verify, including
  [retirement of a local](../mdtests/return_unfold_call_instance_with_local.md)
  and [a direct call](../mdtests/return_unfold_call_instance.md). The general
  proof was written with these unfolds before the final `augment->propagate`
  call and the outcome folds after return.
- Moving `refold_to_root` out of the color-repair module made the theorem
  requirement that `apply` proves by `auto` in
  `rbtree_erase_leaf_wrapper.click` miss; it is now an explicit `have`.

### R3. Automatic unfolding of recursive specification functions

`simp` unfolds a recursive pure function when its argument is a known
constructor, to a fixed fuel, as Dafny does. The unfolded equation is a
checked rewrite in the expansion. This removes most of the 70 explicit unfolds
per arm, and most model-term restating, because the solver can see through
`plug` and `rb_reparent`.

The SMT-backed `auto` ([smt-auto-stage1.md](smt-auto-stage1.md)) keeps
recursive predicates out of scope.
This item is different: it covers pure functions over constructors, which are
bounded and decidable at fixed fuel. It can be added as a stage of that issue
or done separately.

Status (2026-10-16): `simp` unfolds one application over a known constructor
(the smt-auto step-3 work) and now evaluates on to a fuel of eight checked
unfold or rewrite steps, through constructor equations among the facts. The
rewrite of `rbtree_erase_color_flips_red_all.click` that would measure the
saving waits on `bugs/rbtree-sized-flip-loop-object-class-join.md`: the
example does not verify on master today.

### R4. Automatic opening and closing of resources

When a step reads or writes a field covered by a folded recursive resource
whose model is known to be one constructor, `step()` unfolds that layer. At
function exit, loop back edges and arm joins, Click refolds layers whose
fields still match the definition. This follows VeriFast's auto-open/close
and Viper's fold heuristics. It must stay bounded: one layer per access, and
no search over which resource to open. Explicit `fold`/`unfold` remain for
everything else. This targets about 100 lines per arm.

### R5. One script for several goals

Allow one proof block to close several arms whose scripts are the same up to
a renaming. For example:

```click
match c.model {
    Context::Right(id, above, pc, sm, um) | Context::Left(id, above, pc, sm, um) => { ... },
}
```

Each listed arm runs the shared block separately, against its own C path, so
the kernel checks each instance independently. A direction-generic model
layer makes the text identical: `child(d, t)` and `Context::Child(d, ...)`
in place of separate left and right constructors, with lemmas proved once
over `d`.

This is the Lean `<;>` idea restricted to arms, and it involves no
metaprogramming. It does not help where the C differs between arms; such
lines stay per arm.

Measure it after R3 and R4. If they shrink each arm to tens of lines, as in
Dafny, R5 may not be worth its language surface.

Not proposed: checked mirroring of C code. The Linux arms are not textual
mirrors, and checking that two C regions are mirror images is a large new
trusted component.

## Expected effect on rbtree-erase

These are estimates, to be replaced by measurements.

- R1 removes about 29,000 lines.
- In the general proof, the SMT-backed `auto`, R3 and
  R4 target about 400 of 1,377 lines per arm: the 222 one-line equalities,
  the recursive unfolds and the resource bookkeeping. Facts that no longer
  need restating should account for a large share of the remaining `have`s.
- R5 would then halve what remains of the mirrored arms and theorems.

## Validation

- R1: delete the superseded files and port their mutation checks. Record the
  example's line count and gate time before and after.
- R2: done. General `__rb_erase_augmented` and `rb_erase` contracts replace
  16 sidecars (4,815 lines, 37.7 s) with 3 (2,793 lines, 21.1 s); see R2.
- R3 and R4: mdtests for one fuel unfold, one automatic open on a field read,
  and a refold at a join. Add negative cases for an unknown constructor (no
  unfold) and a field mismatch at refold (refused). Then rewrite one arm of
  `rbtree_erase_color_flips_red_all.click` and record its size and time.
- R5: only after R3 and R4 are measured.
