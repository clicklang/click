# Verify the Linux rbtree example on the recursive structure models

Renamed from `recursive-structure-models.md` on 2026-09-13 and collapsed
from its 1600-line journal to the state, the decisions, and the remaining
work. The models, the two syntax extensions (loop binders `owns name:
res(args);`, keyword-free `decreases name;`), decision D7's single
publication point, and packages A1 through A28, T1 through T8, S1, B1
through B3, C1, C1b, C2, C2b, C2c, and C4's replacement half are landed.
What remains is finishing the specific example: the verbatim `__rb_insert`,
the traversals, erase, the augmented callbacks, and attaching the sidecars
to the pinned source. That work is numbered as
[chunks 1 to 24](#remaining-work-chunks-1-to-24), one pull request each. The
full history is in git: `git log --follow issues/rbtree-example.md`.

P1: required for MVR. Linux rbtree does not store keys, so its generic
correctness property is preservation of node identity and in-order order
while links and colors change; a contract that consumes one well-formed
tree and produces another cannot state that without an abstract model.

## State, 2026-10-02

**`__rb_insert` verifies end to end** on the unchanged Linux C
(`examples/rbtree-insert/rbtree_insert.click`, in the example gate), with a
restated contract that produces the fixed-up tree at its focus rather than at
`root->rb_node`; see chunk 7. **`rb_insert_color` does not**: it calls the
inline `__rb_insert`, whose contract Click never applies at a call site.
Both need the owner's decision before chunk 7 can be called complete.

## Priorities, 2026-09-13

Fix what slows the work before completing the example:

1. **Imports first: delivered.** `examples/rbtree-insert` now imports the
   shared `examples/rbtree-model/rbtree_model.click`; its C is unchanged and
   the unfinished proof remains an explicit negative frontier. I1 was the P1
   dependency; all retained import follow-ups are P2 and block neither C3 nor
   C5. C6 depends on callback packaging, not broader imports, unless its final
   design requires a named callback contract to cross a module boundary.
2. **Diagnostics that point the wrong way** (package T9 below), since
   several resumptions lost their budget to them.
3. **Efficiency next, if it stays on pace to be a problem.** `click verify`
   of the insert fixture went from 0.6s to 5.8s with a third of the loop
   body written, largely because the body is spelled out once per frame
   combination. Remove the duplication (a theorem per case, D10 shape),
   then measure; a verifier scaling defect is a blocker under the
   efficiency contract.
4. **Then the remaining exits of C3**, as separate packages by exit path.

## State, 2026-09-26

**C3b is started on the left-left frames.** The model gains
`ctx_insert_case3_left_step` / `_right_step` (in-order, `is_rb_root`, parent
consistency, and the sibling's black root, all stated on the context the loop
hands back at the `break`) and the parent-consistency converse and swap lemmas
they rest on (`plug_parent_consistent_ctx`, `ctx_consistent_swap`). In the
frontier, the black-uncle arm of the cursor-`Left`, grandparent-`Left`
combination runs case 3 to the `break` on six of its eight leaves: the split is
the parent's other child (empty or a node, for `if (tmp)`) times the
grandparent's own frame (`Top`, `Left`, `Right`, for `__rb_change_child`, which
`step()` executes inside one inline call). The report is now at statement 42,
`augment_rotate(gparent, parent)`, with 9 `break`s and 4 `continue`s complete;
`tests/examples.rs` pins it. Verify time of the frontier went from 1.5s to 3.7s
on a warm release build for six new leaves, each about 150 lines of proof;
that is a measurement, not yet a scaling check.

Gaps 74 and 75 below were fixed on the way. The 2026-09-29 recheck on
`f01a85a1a` leaves the frontier unchanged. An immediate sibling refold under
its model identity now passes owned-cell consumption and fails instead at
`selected child does not satisfy the proposed parent model`: the left child's
pointer argument does not match, while its model field does. A small no-write
unfold/refold reduction reproduces this; refolding at the original pointer
passes. The related `p->word` / `id->word` regression already passes.
That historical reduction now passes: checked child-read definitions retain
their graph identity, and the later read-identity recheck accepts the immediate
sibling refold. See the [checked pointer-read design](../docs/internals/equality-closure.md#checked-pointer-read-sources).
The original frontier remains at statement 42; the next `step()` stops on two
successors in the inlined rotation. The completed equality migration does not
establish that those remaining rbtree leaves verify.

The remaining C3b work after that gap: the empty-uncle leaves of the same
combination (the text is the same after refolding the uncle as `Empty`), the
other three combinations (the two inner ones add case 2's rotation first; the
model has `ctx_insert_case2_*` but no `_step` form yet), then C3c.

## State, 2026-09-25

**C3a is written on all four frame combinations.** The uncle-red `continue`
of `__rb_insert` now recolours the uncle, the parent, and the grandparent,
refolds the three nodes at their recoloured models, and closes the nine
invariants and the two-frame `decreases c` descent, for the cursor's frame
`Left` or `Right` inside the grandparent's frame `Left` or `Right`. The C
proof of each arm unfolds one cursor frame with `plug_left_frame` or
`plug_right_frame` and applies one of the new model theorems
`ctx_insert_case1_left_step` / `ctx_insert_case1_right_step`, whose four
conclusions are stated on the explicit recoloured subtree; the parent
consistency half rests on the new colour-erased `Links` skeleton
(`plug_insert_fix_recolor_parent_consistent`). This is the D10 shape E1 asked
for: the case reasoning lives in the model once, and each C arm is the
bookkeeping between the frame's own facts and the theorem's spelling. The
four arms remain written out per D9. The kernel gap it exposed (73 below) is
closed in 9e1c4281.

The loop rule was certified end to end only in a scratch experiment whose C
copy cut the uncle-black paths short with a `break`; on the unchanged source
the frontier report for the first uncle-black path preempted the back-edge
check of the completed paths at the time, so the recolour arms' closers were
validated there by explicit `have`s of every invariant in the rebound binder
spellings immediately before `close_invariants()`. Since the frontier fix the
next day, the finished arms' closers are checked on the unchanged source
before that report. The frontier is now the uncle-black
case, statement 22 of the body (`tmp = parent->rb_right`), which is where C3b
starts on all four copies; `tests/examples.rs` pins that diagnostic. The
frontier verifies to that point in about 2.8s on a warm debug build.

Three tooling limits met on this resumption were fixed the next day: a lone
sidecar now selects a project root covering its imports, so
`rbtree_insert.frontier` verifies from the command line; `--trace-to` reaches
tactics inside proof `match` arms and loop phases; and a finished `preserve`
arm's back edge is checked before an unfinished sibling's frontier is
reported (`mdtests/preserve_finished_arm_checked_before_frontier.md`).

## State, 2026-09-13

**The traversal parser prerequisite:** the unchanged `rb_next` guard
`while ((parent = rb_parent(node)) && node == parent->rb_right)` now parses and
lowers through checked statements. The assignment result has the target's
scalar type, its right operand is evaluated exactly once, the second conjunct
remains short-circuited, and a loop guard reruns the assignment after every
iteration and `continue`. The retained `mdtests/rb_next_conjunctive_guard.md`
now reaches its next bounded proof frontier: `execute()` needs a view of
`node->rb_right` while the entry `rb_at(node)` remains folded. C4b still owns
the complete descent/ascent proof; this support does not claim traversal
verification.

**The insert fixture**, `examples/rbtree-insert`: `rbtree.h` and
`rb_insert_color.c` retain the verbatim Linux `__rb_insert` and
`rb_insert_color` C formerly embedded in `mdtests/rb_insert_color.md`.
`rbtree_insert.click` is a green import/load entry and does not claim the
insert proof is complete. `rbtree_insert.frontier` imports the shared model
and retains the complete contract and unfinished proof; a dedicated regression
requires its bounded failure at statement 23. The loop carries
`owns c: ctx_at(node, root); owns t: rb_at(node); decreases c;` with nine
invariants in the frame-level form the C2c case theorems use:
`is_rb(t.model) == 1` and `ctx_almost_rb_insert(c.model,
black_height(t.model)) == 1` (the black height is the pure function of the
loop-carried model, which is how every case theorem spells its `bh`), plus
the seven link, colour, and order invariants. The contract's `requires`
were restated the same way; the restatement is a faithful strengthening
(the old `almost_rb_insert(plug(c.model, t.model))` and `ctx_root_black`
follow from it). Complete: `initialize`; the root-blackening `break`; the
black-parent `break` on both frames; `Context::Top` refuted for the
grandparent frame; the uncle's arms split. The `expect` line is the
frontier report at statement 23 (`tmp = parent->rb_right`, red uncle
skipped): "still ahead on this path: the body's end and 1 `break`. Already
complete: 2 at a `break`". Remaining: the two recolour `continue`s, the two
rotation `break`s, the body's end, the post-loop `simp()`, and
`rb_insert_color`. The focused imported-frontier regression currently reaches
the expected diagnostic in about 1.3s on a warm debug build; that timing is
supporting evidence, not a new gate, and E1 still owns the per-frame proof
duplication. The fifth resumption's branch draft (the red-uncle `Top` frame,
reading `gparent->__rb_parent_color` after `gparent == cgp`) stopped on
gap 72, a kernel read-permission bug; with it fixed the draft reaches
statement 42, `augment_rotate(gparent, parent)`, in case 2.

**How the last five resumptions went.** Each stopped on one to three
verifier bugs rather than on proof difficulty, every one now closed (gaps
62 through 71 below): typing of proof-arm bindings as memory bases, inline
functions' locals with no layouts, four missed scoping sites, three
`click audit` disagreements with `click verify`, a `contradiction`
accepted only as an arm's sole tactic, and an unfinished `preserve` that
hid its frontier. Expect the same cadence on the rotation exits.

**Landed packages, one line each (commit).** A1 arm selection dff4ebdc;
A2 cross-family arm children de1da207; A3 loop binders 9e62f2a2; A4
structural `decreases` 2ab5dba3; A5 struct-pointer arm bindings as memory
bases 036170c4; A6 pointer payloads and arm scoping 7b52373a; A7 `let r =
step(...)` 9c7710ee; A8 proof `match` of any width 590b2553; A9 proof
`match` at any frontier 66bd8005; A10 wide loads named by load variable
b0cfc0e6; A11 pointer disequality from null-ness or separation ec8ffc4a;
A12 folds read their arm's cells 0e7d8000; A13 refuted arms publish
negative facts, ascent past the contract boundary 6335d1eb; A14 ascending
walks 660c7643; A15 ranked loops call inline helpers 819cb5b1; A16 `ih`
over all theorem parameters 24517c61; A17 short-circuit guard exits
1472f6f8; A18 unfold names its cells b8014f05; A19 read authority common
to possible arms eec257aa; A20 pointer-argument body facts ef856acd; A21
arm refuted from a predicate fact cbf19069; A22 ownership across a proved
pointer equality a6323676; A23 `break`/`continue` in ranked bodies
2b64528d; A24 insert contract blockers 2d84c565; A25 exits joined through
the binders ca49cf06; A26 loop bodies inside proof matches ba0d9c30; A28
one arm-publication point per frontier badc1de3; S1 unevaluable guard
conjunct refused 841126d4; T1 531b5651; T2 92a81e32; T3 bb009743; T4
63ec6190; T5 2cb5669f; T6 2ed15042; T7 b3cfc86a; T8 6426b3d4; B1 (docs
0b6016aa); B2 and B3 688e7990; C1 05257e8e; C1b node-keyed model 368c4aec;
C2 c9d5afee; C2b 427e2463; C2c 181d6db6; C4 replacement half 32992501
(traversals `rb_first`/`rb_last` and the `rb_next` guard are pinned in
`mdtests/rb_first_last.md` and `rb_next_conjunctive_guard.md`; the verbatim
assignment-expression guard now lowers, and the latter fixture records the
next folded-entry proof frontier). Uniform scoping: bb142e1c (theorem arguments,
`instantiate`, `extract`), ad5c2307 (loop clauses), 2d96d5d7 (phase
bodies), 99a07d5c (`using` premises in a `have` body).

**Where to pick this up.** C3b starts from the frontier in
`examples/rbtree-insert/rbtree_insert.frontier` at the `Color::Black` arm of
each `match uncolor`, which stands before `tmp = parent->rb_right` (or
`rb_left`) with the uncle's cells unfolded as `ul`/`ur`, the grandparent
frame unfolded as `us`/`uu`, and `cup == Context::Left(...)`/`Right(...)`
already restated in constructor form. The branch `claude/rsm-c3-insert-fixup-7`
named earlier no longer exists. To iterate on the frontier from the command
line, copy it beside a copy of `examples/rbtree-model` under one scratch
root and verify that directory (see the fixture README). Each resumption so
far was one agent per package with the orchestrator integrating; doing the
packages directly works the same way, the packages below are written to be
self-contained either way.

**Machine notes.** One full gate at a time; under heavy load a few unit
tests hit nextest's 60s kill with zero assertion failures and pass alone.
`scripts/check.sh` prints no marker of its own; judge it by exit status,
and check for a running gate with `pgrep -x -f "bash scripts/check.sh"`
(a plain `pgrep -f` matches its own wrapper shell and deadlocks a queue).
A fresh worktree's cold build is about 90s and 3 GB; build caches grow
with incremental work, so remove worktrees when their task lands. The
other agents' worktrees under `/private/tmp/click-*` held 150 GB of build
caches on 2026-09-13; deleting `target/` of any not touched that day is
safe and was what kept builds possible. sccache was measured and removed:
this crate has 26 registry dependencies worth seconds, and neither the
`click` library (cache key includes the working directory) nor the
binaries and test binaries (they link) are shareable across worktrees.
Two tooling ideas not done: `click audit` on only the `expect pass`
fixtures a commit touches, run at integration rather than in the gate
(three of the last ten bugs were verify passing while audit failed, each
found only by hand); and splitting the unit tests that take over 15s idle.

## Violated invariant

Contracts for a mutable recursive structure must be able to relate its finite
abstract model before and after mutation. The model must be derived from the
owned structure, not supplied as an unconstrained ghost assertion.

## Intended regression

Define an abstract model for a binary tree whose in-order sequence contains
node identities. Verify unchanged left- and right-rotation functions with
contracts showing that:

- the output contains exactly the input nodes;
- the in-order sequence is unchanged;
- parent/child links are consistent; and
- no node is duplicated or omitted.

Negative rotations that drop a subtree, reuse one child twice, or swap the
in-order position of two nodes must fail even if the output can still be
folded as some binary tree.


## Design decisions

These are settled. A package that finds one of them unworkable stops and
reports rather than substituting a different design.

**D1. Model shape.** One `spec enum` per structure, carrying node identity as
a pointer payload, the payload the structure needs, and the submodels. For
the scaffold that is the landed `HeapTree::Node(struct tree_node*, int,
HeapTree, HeapTree)`. For rbtree it is
`RbTree::Empty | RbTree::Node(struct rb_node*, Color, RbTree, RbTree)` with
`spec enum Color { Red, Black }`. Pointers stay pointers: models grant no
ownership and are never converted to integers. In-order node identity is the
derived `List<struct rb_node*>` from a pure `inorder` function; node-set and
multiplicity claims are stated about that list.

**D2. Parent pointers and color live in the node's own arm.** The tree
resource takes the parent as a parameter, `rb_at(p, parent)`, and its `Node`
arm owns `p->__rb_parent_color` and states the packed word. C1 landed it as
two facts, `p->__rb_parent_color == address(parent) + (p->__rb_parent_color
& 1)` and `(p->__rb_parent_color & 1) == color_bit(color)`, because the
single fact with an opaque `color_bit(color)` carries no bound for the
tag-clearing step in `rb_parent`. Children
are `owns left: rb_at(p->rb_left, p)` and `owns right: rb_at(p->rb_right, p)`.
Parent/child consistency is therefore a body fact, not a separate claim, and
no witness inside a matched body is required. Acyclicity is inherent in a
finite inductive model over linearly owned nodes. The root cell
`root->rb_node` is owned by the context's `Top` frame (D3), with the root's
parent word stating a null parent.

**D3. Bottom-up algorithms use a context (zipper) resource.** Linux insert
and erase start at a node and climb parent links. The proof state holds the
ancestors as a linear stack of frames:

```click
spec enum Context {
    Top,
    Left(struct rb_node*, Color, RbTree, Context),
    Right(struct rb_node*, Color, RbTree, Context),
}

resource ctx_at(child: struct rb_node*, root: struct rb_root*) {
    field model: Context;
    match model {
        Context::Top => { owns root->rb_node; fact root->rb_node == child; },
        Context::Left(parent, color, sibling_model, up_model) => {
            owns parent->__rb_parent_color;
            owns parent->rb_left;
            owns parent->rb_right;
            owns sibling: rb_at(parent->rb_right, parent);
            owns up: ctx_at(parent, root);
            fact parent != 0;
            fact parent->rb_left == child;
            fact sibling.model == sibling_model;
            fact up.model == up_model;
        },
        Context::Right(...) => { /* mirror */ },
    }
}

function plug(ctx: Context, sub: RbTree) -> RbTree decreases ctx { ... }
```

`plug` rebuilds the whole model from a context and the focused subtree.

Amendment after C1 (2026-09-12): the frame takes the focused child's parent
as a resource parameter, `ctx_at(child, parent, root)`, exactly as `rb_at`
takes it. `Top` states `parent == 0`; `Left(grandparent, color,
sibling_model, up_model)` owns `parent`'s cells and `up: ctx_at(parent,
grandparent, root)`. A frame keyed only by the child needs a pure accessor
from `ctx.model` to the parent pointer in its contracts, and pure functions
cannot return pointers (gap 8); with the parent as an argument, contracts
and loop binders name it as the C local the Linux loops already maintain
(`parent = rb_red_parent(node)`), and no accessor is needed. C1's fixtures
use concrete frames and predate this amendment; C3 adopts it.
Every loop invariant in the rbtree algorithms has the form
`inorder(plug(ctx.model, sub.model)) == inorder(old(t.model))` plus the
algorithm's shape predicate. `ctx_at` contains `rb_at`; `rb_at` never contains
`ctx_at`, so the mutual-recursion rejection is untouched. The scaffold uses
the same construction without color or the root struct.

**D4. Contract interface for bottom-up entry points.** `rb_insert_color`,
`__rb_erase_augmented`, and `____rb_erase_color` are contracted over a context
plus focused subtree at the given node, not over a whole tree plus a
membership witness. A top-down tree cannot locate an arbitrary member
without a path, and insert callers build the context in their own descent
loop anyway. Whole-tree wrappers relate `ctx_at(node, root)` and
`rb_at(node, parent)` to the entry model through `plug`. The consequence for
callers of the verified erase is documented, not hidden.

**D5. Loop binders reuse the contract binder syntax.** A loop header may
declare `owns name: resource(args);`. Semantics mirror a callee contract:

- `initialize` consumes the unique enclosing owned instance whose family and
  arguments match, and binds `name`. Ambiguity is an error. No binder map in
  the first slice.
- The body holds `name`; invariants read `name.field`; unfold and fold work
  as in any proof. Undeclared instances are unavailable in the body and
  returned after it, which is the existing exclusive-instance rule.
- `close_invariants()` selects the instance the same way with the arguments
  re-evaluated in the current state, rebinds `name` to it whatever the body
  called it, and checks the invariants against its fresh fields. This is what
  lets a body hand a child `l` to the next iteration: after `root =
  root->left`, `l` is `tree_at(root)` by proved argument equality.
- After the loop, `name` denotes the final instance at the final arguments.
- A loop name may reuse an enclosing binder name; that is a rebinding.
  `old(name.field)` keeps its meaning, the function-entry instance of the
  function-level binder. No loop-entry snapshot in the first slice.
  Landed behavior (A3): a loop binder takes the unique owned instance of its
  family with provably equal arguments and renames it, so a fresh name
  consumes the enclosing name for the rest of the function and cannot appear
  in `ensures`; reuse the enclosing name. The head gives the binder fresh
  fields, so its model at the head is exactly what the invariants state.

**D6. Structural loop measure is `decreases name;` with no keyword.**
Functions and resources share one namespace (declaring both is rejected), so
`decreases` measures are parsed as one expression and classified after
resolution: an integer expression, a resource application such as
`list(node)`, a loop or contract binder such as `sub`, or an ADT parameter in
a pure function. The existing `decreases resource list(node)` spelling is
replaced by `decreases list(node)`; `src/surface/parser.rs` currently
branches on the `resource` keyword before resolution and stops doing so. The
back-edge rule is the function-level one: the instance rebound to the name
must be a direct contained child, in the exact resource definition, of the
instance the name held at the loop head, checked from the unfold that
exposed it. Descending loops decrease `sub`; ascending and
rotate-then-ascend loops decrease `ctx`, because a rotation may grow the
subtree but the context strictly loses a frame.

**D7. Arm selection from requirements, one mechanism for contracts and loop
heads.** When a section's requirements together with constructor
exhaustiveness entail exactly one arm of a matched instance, lowering
exposes that arm's cells as read authority and its facts as assumptions,
with the arm's bindings as fresh symbolic values. `c.model != None` on a
two-constructor enum and `exists (v) { c.model == Some(v) }` both select
`Some`. If no single arm is entailed, the composite stays folded and reads
through it fail as today; there is no implicit proof by cases. The same
decision applies at a loop head, where the invariants play the role of the
requirements, so a guard such as `root->left != 0` can read through the
focused subtree. This generalizes the existing decidable-guard expansion in
`src/kernel/functions.rs` (`expand_decidable_composite_resource_frontier`)
rather than adding a second path. No sugar such as `requires c.model is
Some` in this issue.

**D8. Matched arms may own children of another declared resource.** The
same-family restriction in `algebraic_types.rs` is lifted. Child field
equations, the explicit child map on fold, `let { ... } = unfold(...)` naming, and
the acyclicity check across definitions all apply unchanged. Mutual
resource-definition cycles remain rejected.

**D9. No new resource algebra and no automatic unfolding.** No ghost state,
fractions, magic wands, or `auto` fold search. Every layer a proof needs is
named. Reasoning and certificates stay output-sensitive in the explicitly
exposed model terms; each rebalancing case is an explicit sequence of
unfold, C steps, fold, and `have`. Symmetric cases are written out; proof
reuse across mirrored cases is not a goal of this issue.

**D10. Pure library.** `inorder`, membership, `black_height` over `Nat`,
`is_rb`, and the almost-red-black predicates for insert (one red-red
violation at the cursor) and erase (one black deficit at the cursor) are
pure functions and predicates with induction theorems. Rotation, splice, and
recolor lemmas are stated over models and proved once; C proofs apply them.

**Deferred language questions.** Decided 2026-09-11 to add no language
beyond D5 and D6. The following stay out of scope for every package here:
resource-transforming lemmas (which would give a reusable "focus the tree at
a member" step and proof reuse across mirrored cases), a binder map on loop
headers, loop-entry snapshots such as `at(loop.entry, sub.model)`, and a
positive constructor test such as `requires c.model is Some`. A package that
appears to need one reports the need instead of adding it.


## Closed gaps

Every gap found during the campaign, one line each, with the package or
commit that closed it. Reproductions live in the named fixtures.

| Gap | What | Closed by |
|---|---|---|
| 1 | A loop could not hold a modeled instance | A3 |
| 2 | Model-gated composite exposed no cells at contract lowering or loop heads | A1 |
| 3 | A matched arm could own only its own resource's children | A2 |
| 4 | `decreases` accepted only integers | A4 |
| 5 | Struct-pointer constructor binding not a memory base | A5 |
| 6 | Pointer payload not relatable to a C pointer | A6 |
| 7 | Structural termination ignored matched bodies | A4 |
| 8 | Pure function could not return a pointer | A6 |
| 9 | Call result in a condition had no name | A7 |
| 10 | `if` expression could not produce an algebraic value | A6 |
| 11 | Audit disagreed with verify on the scaffold | T1 |
| 12 | Proof `match` capped at two constructors | A8 |
| 13 | Loop body could not unfold its binder | A9 |
| 14 | Audit failed on other examples | T3 |
| 15 | Wide proof matches superlinear | T4 |
| 16 | Fold inside an arm lost unwritten-cell facts | A10 |
| 17 | Remaining audit disagreements | T5, T6 |
| 18 | Pointer disequality not decided from null-ness or separation | A11 |
| 19, 20, 24 | D3 frame fold and pointer-payload ownership, one bug | A12 |
| 21, 25 | Struct-pointer local had no struct layout | A12 |
| 22 | Separation from separate unfolds did not reach a later frontier | A17 |
| 23, 28 | Stale; `_Bool`/float loads unnamed | T6 |
| 26 | Selected-arm facts at contract lowering broke nine fixtures | A13 |
| 27 | Refuted arm not published as a negative fact | A13 |
| 29 | Ascending walk stopped at the contract boundary | A13, A14 |
| 31 | Soundness: unevaluable guard conjunct dropped | S1 |
| 32 | Induction hypothesis fixed every non-inducted parameter | A16 |
| 33 | Ranked loop could not call a contract-less inline helper | A15 |
| 35 | Parent-as-parameter unspellable; model re-keyed by node | C1b |
| 36 | Two evaluable guard conjuncts refused | A17 |
| 37, 38 | Load identity across an unfold | A18 |
| 39 | Guard prefix did not publish common read authority | A19 |
| 41 | Soundness: capture in pure-function unfold | C1b |
| 42, 43 | Pointer-argument body facts; payload-to-local identity | A20 |
| 44 | Two `RbTree` shapes | C2b |
| 46, 50 | `rb_replace_node_with_children` 17s; repeated work | T7 |
| 48 | Arm not refuted from a predicate invariant | A21 |
| 51 | Owned cells did not follow a proved pointer equality | A22 |
| 53 | Insert fixup parse and contract blockers | C3 (cffe7116), A23, A24, C2c |
| 54 | `break` exits had to reach one state | A25 |
| 55 | Omitted-phase planner and expansion defects | T8 |
| 56, 57 | Proof `match` around a ranked loop; `branch` in `preserve` | A26 |
| 59 | Soundness: `do ... while` exported no guard-false exit | A25 |
| 61 (a) | Contract-lowering refutation from an arithmetic requirement | A28 |
| 62 | Phase bodies did not see a proof `match` arm's bindings | 2d96d5d7 |
| 63 | Unfinished `preserve` hid its frontier | 6e81426b |
| 64 | `old(t.model)` after a pre-loop unfold hit `Paths` | 3893e6b5 |
| 65, 66 | Smart `have`s and helpers inside `initialize by { }` did not expand | 54d0f136 |
| 67 | Load through a proof-arm binding with a pure call: arm bindings were untyped in proof arms | 9a49463d |
| 68 | `simp() using` premise in a `have` body could not name an arm binding | 99a07d5c |
| 69 | Consumed instance's arm equation cited by a spelling that no longer lowered | 44acfb0c |
| 70 | `static inline` locals had no layouts (map keyed by the `#inline:` name) | ca8b75f8 |
| 71 | `contradiction` in a `preserve` arm only as its sole tactic | ccf9a340 |
| 72 | A read through a symbolic identity proved equal to a C pointer was refused: the read lookup resolved to the alias and looked only there | a3b96c12 |
| 73 | `if (parent != tmp)` undecided with both nodes owned: the separation rule read only assumed compositions, and two instances opened one at a time never shared one; a comparison now composes its own two holders through the alias component | 9e1c4281 |
| 74 | A fold's arm fact lowered a frame identity through its proved-equal C local inside a pure-function argument, so the fact proved in the model's spelling did not count; body facts are now also matched after substituting one pointer by an exact alias | this change (frontier leaves) |
| 75 | `rewrite(p == 0)` did not reach `(uint64)p` in a 64-bit goal, and `address(null)` was opaque to `normalize` | this change, `mdtests/rewrite_pointer_null_into_an_address.md` |

## Open findings, not scheduled

Small items found along the way and recorded in the fixtures named. None
blocks C3; each is a candidate package when it starts to.

- **Diagnostics** (package T9, landed 14d6e92c): a lowering whose every
  path ends in a runtime error now names the error (a typed load that does
  not fit its cell names its width, pointer, and the value found); a
  refused `rewrite` prints the lowered equality and goal; a refused fold
  names which fact of which arm; a failed contract resource transition is
  described rather than dumped; an empty `preserve` arm is named in the
  frontier report. Not reproduced, no change: the clause-position note
  naming the wrong clause; "could not apply checked contract resource
  effect" for an unproved produced-model claim (the shapes tried report an
  unclosed goal). Closed 2026-09-14: a justified 64-bit bit-test inequality
  now expands to its selected equality rewrite and a checked context-free
  normalization; `mdtests/wide_inequality_certificate.md` retains the pure
  regression and its required set-bit premise.
- **Pure-proof limits:** `normalize()` and `normalize() using` do not
  close pointer-equality transitivity or symmetry inside a pure theorem
  (`simp()` does; `rewrite(a == b); normalize();` substitutes a pointer
  equality into a constructor argument while `normalize() using` does
  not); a raw `if parent == p` as a pure function's outermost test unfolds
  to one opaque bitvector operation, so predicate tests are written `if
  <int32 test> == 1`; `extract` directly inside a `match` arm is
  unsupported (gap 52).
- **Loop exits:** algebraic model values are not renamed at the exit
  join, so an exit whose binder model is the head's symbolic model leaves
  an unspellable name in its disjunct; `simp` cannot eliminate an exported
  exit disjunction or substitute an exported loop equation (`cases(...)`
  works); two ascent loops in one function fail the second loop's
  `close_invariants` with plain guards; `click expand` of a `loop` whose
  `preserve` has `match`, `unfold`, and a proof `if` with `initialize`
  omitted emits a script failing with "resource match requires constructor
  evidence" (gap 60, T5/T8 class, an audit disagreement worth a T package
  when a fixture hits it).
- **Folds and unfolds:** a body that reassigns a parameter cannot refold
  its borrowed instance at the entry position (`fold(tree_at(old(root)),
  ...)`; arguments are current-state only); an unfold of an unmatched
  composite leaves its cells unnamed; a `have color_bit(Color::Red) == 0`
  before a refold breaks the fold's exact body-fact check; a cell reached
  neither by contract materialization nor by an unfold loses its load
  identity across a write whose separation is only a resource fact.
- **Proof shapes:** the grouped driver declines a top-level `match
  c.model` after a loop while the same shape on the subtree binder works;
  a proof `if` whose arms contain a proof `match` at the top level of a
  function proof is declined by the grouped driver.
- **Not uniform:** while a contract section's clauses are evaluated one at
  a time only read authority is published, not a full arm re-decision,
  because a per-clause re-decision broke the near-linear width contract
  (A28).
- **Pointer spellings across a write or a fold:** a fold at an arm identity
  after a store to another owned node now verifies (chunk 1). The logical
  form is still open and filed as
  `bugs/arm-identity-read-differs-from-parameter-read-after-a-store.md`:
  after such a store, `have id->right == p->right` is refused although
  `have p == id` holds. Loads in fold arguments
  (`fold(rb_at(x->left), ...)`) are unsupported.
- **Stale prose:** `mdtests/rb_replace_node.md` says a victim with
  children cannot be contracted, which `rb_replace_node_with_children.md`
  contradicts.

## Remaining work: chunks 1 to 24

Renumbered on 2026-10-02, and the importer chunks again the same day once
the pinned source was measured. A **chunk** is one pull request: one coherent green
commit series with its regressions and docs. C is fixed; adaptation goes into
contracts, lemmas, resources, tactics, lowering, or the kernel. No chunk
creates issues. A chunk that hits a tooling failure listed in `AGENTS.md`
stops and reports; if the failure needs its own kernel fix, that fix is its
own pull request ahead of the chunk.

The dated state sections, decisions, and tables elsewhere in this file, and
some fixtures and other issues, still use the earlier package names. They map
as follows:

| Earlier name | Now |
| --- | --- |
| I1 (imports), E1 (per-frame duplication), C3a (recolour `continue`s) | landed |
| C3b (rotation `break`s) | chunks 1 to 6 |
| C3c (post-loop and `rb_insert_color`) | chunk 7 |
| C4b (traversals) | chunks 8 and 9 |
| C5 (erase) | chunks 10 to 13 |
| C6 (augmented variants and callbacks) | chunk 14 |
| [kernel-scale-preprocessing.md](kernel-scale-preprocessing.md), [linux-rbtree-inline-helpers.md](linux-rbtree-inline-helpers.md) | chunks 15 to 23 |
| D1 (attach sidecars to the pinned source; not design decision D1) | chunk 24 |

Chunks 8, 10, and 15 have no unlanded prerequisite; chunk 3 is landed. None depends on the
[authority migration](authority-migration.md): the rbtree fixtures use neither
`count(...)` nor `guarded_by`.

### Insert

Case 1 (uncle red) is written on all four frame combinations and every tactic
is checked on the unchanged source; the loop rule itself is certified once
the uncle-black arms also end, which is chunk 6. Measure verify time again as
the rotation arms land: a superlinear step is a scaling regression under
`docs/internals/verification-efficiency.md`.

**Chunk 1. Last two left-left leaves: landed 2026-10-02.** The two case-3
leaves under a `Right` great-grandparent frame in the cursor-`Left`,
grandparent-`Left` combination run to the `break`: the sibling `xs` is
unfolded so that `parent->rb_left == old` in the inlined `__rb_change_child`
is decided, `step()` runs the rotation, and `xs` is refolded at its arm
identity with `fold(rb_at(yid), ...)` before the frame refolds the finished
leaves already use. The frontier report is now at statement 23,
`tmp = parent->rb_right`, with 11 `break`s and 4 `continue`s complete;
`tests/examples.rs` pins it.

Two earlier readings of this leaf were wrong. The "two statement successors"
stop reported on 2026-09-30 was not a kernel gap: it appears only when `xs`
is refolded before `step()`, which hides the cells that decide the test. The
refusal of the post-step refold (`selected child does not satisfy the proposed
parent model`) was not a missing read identity across the rotation's stores
either. The unfold's cells were still cached as a seeded run, and the load of
`yid->rb_left` missed its slot because the run lookup reached the run's base
only through an alias index keyed by the exact pointer, so `id` found the run
at `p` and `id + 8` did not. The lookup now asks the equality graph for the
load's address in the run's block
(`mdtests/fold_at_arm_identity_after_store_to_other_node.md` and three
negatives; see
[the equality-closure note](../docs/internals/equality-closure.md#checked-pointer-read-sources)).

**Chunk 2. Empty-uncle leaves of left-left: landed 2026-10-02.** All eight
leaves under an empty uncle run case 3 to the `break`. The uncle is refolded
as `fold(rb_at(tmp), { model: RbTree::Empty })` with
`rb_root_black(RbTree::Empty) == 1` by unfolding, and the rest is the
node-uncle arm's text with the uncle model spelled `RbTree::Empty`; the arm
starts one statement earlier than the old three-`step()` stub left it, at the
join after `if (tmp && rb_is_red(tmp))`. The frontier report named this path
before the change (checked by advancing each empty-uncle leaf one step: only
this one moved the report, although the report's `tactic@` line points at the
last leaf in the file). It is now at statement 52, `tmp = parent->rb_left`,
with 19 `break`s and 4 `continue`s complete; `tests/examples.rs` pins it.
Verify time of the frontier on a release build, user seconds, load average
about 10: 3.1 with 9 `break`s, 3.2 with 11, 4.3 with 19.

**Chunk 3. Case-2 step theorems — landed 2026-10-02.**
`ctx_insert_case2_left_step` / `_right_step` state the model between the
case-2 rotation and the case-3 code, with conclusions in the spelling
`ctx_insert_case3_*_step` takes with parent and cursor exchanged.
`ctx_insert_case2_left_exit_step` / `_right_exit_step` chain the two and
conclude on `plug(up2, rotated subtree)`, because `node` is the subtree root
at this `break`. The exit spelling was inferred from the C and the finished
left-left leaf; chunk 5 is its first consumer.

**Chunk 4. Right-right combination: landed 2026-10-02.** The mirror of
left-left, case 3 only: sixteen leaves, eight under a black node uncle and
eight under an empty one. The text is the left-left arms' with the cursor,
grandparent, and uncle frames spelled `Context::Right`, the rotated
grandparent's children exchanged
(`RbTree::Node(gparent, cid, Color::Red, uncle, rb_reparent(csib, gparent))`),
and `ctx_insert_case3_right_step` in place of the left theorem; the
great-grandparent frame split, including the unfold of its sibling before
`__rb_change_child`, is unchanged. No lemma was added. The frontier report
stays at statement 52, `tmp = parent->rb_left`, now with 35 `break`s and 4
`continue`s complete; `tests/examples.rs` pins it. The reported path is the
node-uncle black arm of the cursor-`Left`, grandparent-`Right` combination
(chunk 6), checked by advancing each of the four remaining stubs one step.
Verify time of the frontier, release build, user seconds: 4.6 with 19
`break`s and 7.0 with 35, measured together at load average 18, so about
0.15 per leaf against 0.14 for chunk 2.

**Chunk 5. Left-right combination: landed 2026-10-02.** The cursor-`Right`,
grandparent-`Left` combination with a black uncle runs case 2's rotation at
the parent and then case 3 to the `break` on 32 leaves: the uncle (node or
empty) times the cursor's left child (empty or a node, for the first
`if (tmp)`) times its right child (for the second) times the
great-grandparent's frame (`Top`, `Left`, `Right` with an empty or a node
sibling). Each leaf refolds the old parent at
`RbTree::Node(cid, nid, Color::Red, csib, rb_reparent(nleft, cid))` before
`parent = node`, the grandparent at
`RbTree::Node(gparent, nid, Color::Red, rb_reparent(nright, gparent), uncle)`
after `__rb_rotate_set_parents`, and the cursor over both as the new subtree
root; the loop's context binder at the `break` is the great-grandparent's
frame itself, refolded at `node`. `ctx_insert_case2_left_exit_step` supplied
the three whole-tree facts and both children's black roots in the spelling
the arm needed, so the model is unchanged. The frontier report stays at
statement 52, `tmp = parent->rb_left`, now with 67 `break`s and 4
`continue`s complete; `tests/examples.rs` pins it.

The arm needed one tooling fix first, its own pull request: a `step()` in a
`preserve` body was charged to the enclosing `loop`, whose single budget the
sixteenth new leaf exhausted. Verify time of the frontier, release build,
user seconds at load average 5 to 10: 7.1 with 35 `break`s, 11.3 with 51,
14.9 with 67, so 0.26 and 0.22 per leaf for the two halves of this chunk
against 0.15 for chunk 4's shorter leaves; counted work is 77,000 and 67,000
units per leaf against 68,000. The marginal cost of same-shaped leaves does
not grow with the size of the proof.

**Chunk 6. Right-left combination: landed 2026-10-02; the loop rule is not
yet certified.** The mirror of chunk 5 on the cursor-`Left`,
grandparent-`Right` frames, 32 leaves through
`ctx_insert_case2_right_exit_step`, model unchanged. Every path of the loop
body now ends: 3 early `break`s, 96 rotation `break`s, and 4 `continue`s. The
frontier report is gone, and the loop rule itself is refused:
`loop exits reach different states, so they have no common successor: memory,
resource ownership`, which `tests/examples.rs` now pins. The exits hold the
same binders and bytes in different representations (the two binders in
different fold orders, cells cached as concrete cells at some exits and as
run slots at others), and the exit join compared them structurally. That is
fixed: the join now compares cells and merged resources, and joins the record
of automatic storage the rotation exits' helper call leaves
(`mdtests/loop_break_exit_after_a_call_with_a_local_joins.md`). The loop rule
certifies, and `tests/examples.rs` pins the post-loop frontier, so chunk 7 can
start. Verify time of the
frontier, release build, user seconds, back to back at load average 8 to 10:
15.0 with 67 `break`s, 18.3 with the first sixteen leaves here, 27.4 with all
of them and the join. Counted work is 4.63, 5.86, and 6.94 million units, so
the second step adds 1.08 million units but 9.1 seconds: the exit join over
99 exits takes several seconds its work count does not show.

**Chunk 7. Post-loop: `__rb_insert` landed 2026-10-02; `rb_insert_color`
is not proved.** The three early `break`s (root and black parent on both
frames) now state the facts the rotation `break`s already did,
`is_rb_root(plug(c.model, t.model)) == 1`, in-order preservation, and parent
consistency, through `ctx_insert_root_exit` and
`ctx_insert_black_parent_exit` (the root `break` refutes a framed context by
unfolding it for `identity != 0`). All 99 exits state them identically, so
they survive the exit join as ordinary facts, and the post-loop proof folds
the loop's two binders into the result and closes with `step(); simp();`.
No kernel change was needed for the proof.

The contract changed. It produced `ctx_at(root->rb_node, root)` and
`rb_at(root->rb_node)`, which no finite proof can reach: the fixup stops at a
focus with any number of context frames above it, and folding them back to
the root is one `fold` per frame, with no C loop to carry an invariant. It now
produces `rb_tree_at(root)`, a resource over `RbFocus::At(focus, ctx_model,
sub_model)` that owns `ctx_at(focus, root)` and `rb_at(focus)`, and states
the three properties of `focus_tree(tree.model)`, which is
`plug(ctx_model, sub_model)`. The footprint, `root->rb_node` included, and
the whole-tree model are the same. This needs the owner's review: it is the
bottom-up form of D4, and callers that want the root form face the same
unbounded fold.

`rb_insert_color` is not proved. Its only statement calls
`static __always_inline __rb_insert`, and Click executes an inline helper's
body at every call site and never applies its contract (documented in
`docs/reference/language/c0.md`), so a proof would have to run the fixup loop
again inline, without invariants. Executing that symbolic loop also runs
away instead of failing promptly:
`bugs/inline-helper-symbolic-loop-call-runs-away.md`. A call step's binder
map on an inline helper was refused as if the call were missing; it is now
refused by name (`mdtests/call_step_binder_map_on_inline_helper_rejected.md`).
Proving `rb_insert_color` needs a decision about verified contracts of inline
helpers, which this chunk does not make.

`examples/rbtree-insert/rbtree_insert.click` is now the proof and passes in
the example gate; the `.frontier` file is gone. `tests/examples.rs` keeps the
C's SHA-256 pins and refuses the proof against an in-memory copy of the C
whose root case skips `rb_set_parent_color(node, NULL, RB_BLACK)` (refused
at the proof's claim that the colour bit is black). `click audit` now selects
the same project root as `click verify`, so it can audit a sidecar that
imports a sibling project's model. Verify time, release build, one run at a
time, load average 2 to 4: 30.6 to 32.7 seconds wall, 5.1 GB peak, between
15.5 and 16.0 million counted units; the chunk-6 frontier, on the same build,
also counts between 15.5 and 16.0 million and took 32.4 seconds at load 0.4.
The 6.94 million chunk 6 reported was on a tree without the loop-exit scaling
pull request, which charges work that was not counted before.

### Traversals

`mdtests/rb_first_last.md` already proves `rb_first` and `rb_last`: both
structural results and their positions in the entry tree's in-order sequence,
with the null result and structural ownership preserved on an empty tree. The
assignment-expression parser/lowering prerequisite is delivered for simple
scalar variable targets, including the unchanged `rb_next` guard.

**Chunk 8. `rb_next`.** The complete descent and ascent on the node-keyed
model, on the verbatim body. Certified (2026-10-02): `mdtests/rb_next.md`
proves the successor contract on the unchanged body, with `RB_EMPTY_NODE`, the
descent, the ascent loop (`decreases t;`, `decreases c;`) and the section after
it; `mdtests/rb_next_rejects_a_dropped_context.md` is the negative. One
translation remains: the parameter is declared without `const`, because C0
keeps `const` across the explicit cast in `return (struct rb_node *)node;`
(`mdtests/rb_next_const_signature.md`). Restoring it waits on the importer's
const-dropping cast rule. A predecessor claim is refused only by `simp`
exhausting its budget (`bugs/simp-exhausts-its-budget-on-a-false-list-postcondition.md`),
so there is no wrong-position negative.

**Chunk 9. `rb_prev`.** The mirror of chunk 8. Certified (2026-10-02):
`mdtests/rb_prev.md` proves the predecessor contract on the Linux body, with
`mdtests/rb_prev_rejects_a_dropped_context.md` as its negative. The model's
list lemmas are not symmetric, so it adds `ctx_descends_from_left`,
`ctx_is_left`, `plug_predecessor` and `rb_inorder_first_through_left`. Its
parameter is declared without `const` for the same reason as chunk 8's.

### Erase (D3, D4, D10)

Larger than insert; expect the same cadence of verifier gaps, and expect this
split to be revised once chunk 11 is under way.

**Chunk 10. Erase model theorems: rebalancing half written 2026-10-02.** One
theorem per `____rb_erase_color` case and side, in the D10 shape of
`ctx_insert_case*_step`, all stated on the loop state the C holds: the cursor
subtree `t` (`node`, possibly empty) is red-black with a black root, and the
context at its parent is valid for a black subtree one level taller,
`ctx_rb(Context::Left(parent, above, pcolor, sibling, up),
Nat::Succ(black_height(t)), Color::Black) == 1` (or `Right`), with the parent
consistency of the whole tree:

- `ctx_erase_case1_{left,right}_step`: red sibling, rotate at the parent. The
  new context is `Left(parent, sibling, Red, rb_reparent(sl, parent),
  Left(sibling, above, Black, sr, up))` (mirrored on the right), which carries
  the same deficit; the new sibling's root is black.
  `ctx_erase_case1_{left,right}_parent_black` gives the parent's colour.
- `ctx_erase_case2_{left,right}_red_exit`: black sibling with black children
  and a red parent; the recoloured subtree makes the whole tree
  `is_rb_root`.
- `ctx_erase_case2_{left,right}_black_step`: the same with a black parent;
  the deficit moves to the parent's subtree in `up`. `ctx_erase_root_exit`
  closes the walk when `up` is `Top`.
- `ctx_erase_case3_{left,right}_exit`: near child red (case 3, then case 4).
- `ctx_erase_case4_{left,right}_exit`: far child red.
- `ctx_erase_{left,right}_sibling_is_node`: the sibling is not empty, so the C
  may read its children.

Every exit theorem states in-order preservation, `is_rb_root`, and parent
consistency on `plug(up, rebuilt subtree)`; every step theorem states them on
the new context. Helpers: `rb_inorder_node_congruence`, `ctx_rb_black_focus`,
`node_color_ok_black_children`, `ctx_erase_case2_left_sibling`. The model
verifies and `click audit` of it passes.

Still open in this chunk: the two-child splice in the form chunk 11 needs.
`rb_erase_two_child_splice` and its parent-consistency twin state the in-order
and link facts of replacing the erased node by its successor, but not where
the black deficit lands when a black successor with no right child is
removed. That is a position inside the right subtree's left spine, so stating
it as a rebalancing start (`ctx_rb(..., Nat::Succ(Nat::Zero), Color::Black)`
at the hole) needs a context for that spine joined to the context above the
erased node, for example a `ctx_concat(inner, outer)` with
`plug(ctx_concat(inner, outer), sub) == plug(outer, plug(inner, sub))` and the
matching `ctx_rb` lemma. The spelling should follow the descent loop chunk 11
writes.

**Chunk 11. `__rb_erase_augmented`.** The unlink in its no-child, one-child,
and two-child cases, contracted so the in-order sequence loses exactly the
designated node. Depends on 7 and 10.

**Chunk 12. `____rb_erase_color`, left-sibling cases.** A checked measure on
every continuing back edge. Depends on 11.

**Chunk 13. `____rb_erase_color`, right-sibling cases, and `rb_erase`.** The
mirror of chunk 12; the exit model is red-black; a negative. Depends on 12.

### Augmented

**Chunk 14. Augmented variants and callbacks.** `__rb_insert_augmented`,
`rb_erase_augmented`, and the propagate/copy/rotate callbacks over an
abstract augmentation. Depends on 7 and 13. The callback and resource
transport it needed landed on 2026-09-15 (one contract interface, one
checked transition per application, dependent clause sets carried across
calls; see [the architecture note](../docs/internals/architecture.md) and
`mdtests/rb_augment_callbacks_helper_*.md`). The 2026-09-14 globals
audit adds `mdtests/rb_augment_callbacks_const_suite.md`: the unchanged const
callback-table caller and a package with read-only fields. It passes under the
shipped stable-view semantics (an earlier candidate-mode refusal was resolved
before the cutover recorded in
[the stable views record](../docs/internals/stable-views.md)), while the
broader [global initializer issue](global-variables.md) is P2. Keep the table
const and preserve the callback guarantees; the no-op fixture is not evidence
for the complete mutation-capable augmentation proof.

### Pinned source

The in-repository import fixture is a demonstration arrangement, chosen for
expedience; work that uses imports is expected to move out of this
repository. Click imports only the checked dependency closure of the verified
rbtree functions, about 80 of the 2,575 file-scope declarations in the
preprocessed unit, and makes no claim about the rest. A declaration inside
the closure that is unsupported is rejected, not dropped. Export storage and
`.export_symbol` assembly are outside the closure and outside the claim.
The measured inventory is in
[kernel-scale-preprocessing.md](kernel-scale-preprocessing.md).

Landed or in the merge queue: variadic prototypes retained as uncallable
declarations, and the
pinned closure `integrations/linux-rbtree/` with its gate test and measured
frontier. `typeof`, statement expressions, and `__builtin_expect` were
already supported.

Chunks 15 to 20 are independent of each other but edit the same parser, so
they run serially. Each moves the first rejection pinned in the gate.

**Chunk 15. Character-literal escapes.** Octal and hexadecimal escapes; the
current first rejection is `'\001'` at `include/linux/printk.h:21`.

**Chunk 16. Declaration-only attributes.** `__gnu_inline__`, `__unused__`,
and `no_instrument_function` on `static inline`, with near-miss negatives;
`gnu_inline` on a non-static inline stays rejected.

**Chunk 17. Unnamed parameters** in body-less prototypes (eight in
`rbtree.h`).

**Chunk 18. Static non-inline file-scope functions**
(`rb_left_deepest_node`).

**Chunk 19. Qualifier and conditional typing.** The const forms in `rb_next`,
`rb_prev`, and the postorder functions, and the conditional-operator type in
`__rb_erase_augmented`, by the actual C rules.

**Chunk 20. `compiletime_assert` and `__builtin_constant_p`.** Block-scope
`extern` declarations with `noreturn`/`error`, and a constant-p semantics
under which the code Click verifies in `rcu_assign_pointer` is the code the
pinned compiler compiled.

**Chunk 21. Checked dependency-closure projection.** Depends on 15 to 20.

**Chunk 22. Recorded compiler-option profile and lock.** Accept a recorded
option only where ignoring it cannot make Click accept what the compiler
treats differently; then a real import lock replaces the negative gate.
Depends on 21.

**Chunk 23. Pinned inline helpers.** The actual `rbtree.h` and
`rbtree_augmented.h` inline bodies as called from the pinned source, per
[linux-rbtree-inline-helpers.md](linux-rbtree-inline-helpers.md). Depends on
22.

**Chunk 24. Attach the sidecars to the pinned translation unit** and replace
the verbatim-copy fixtures with the pinned regression. Depends on 9, 14, and
23.

## Structural termination audit, 2026-09-14

Audited at `61a3ce92`. The separate `structural-loop-termination` issue is
retired: its missing-language-feature diagnosis predates A4 and the subsequent
loop work. The remaining algorithm proofs stay P1 in C3, C4b, and C5 here;
retiring the duplicate issue does not establish termination of unfinished
insertion, erase, or successor/predecessor proofs.

The implemented spelling is `decreases sub;` for a loop resource binder and
`decreases list(node);` for a function resource measure. The back-edge rule is
**strict contained descent**, including multiple exposed child layers, rather
than only one direct child. It compares the finite inductive model carried by
the rebound instance with submodels named by the exact resource definitions
and the selected constructor premises. A fresh instance name does not by
itself prove progress. Kernel `loop_structural_descent_failure` in
`src/kernel/loops.rs` supplies the check for loop execution and the proof-object
loop join in `src/surface/proof/proof_object/execution_statements.rs`.

| Original requirement | Current evidence and remaining scope |
| --- | --- |
| Descend through children without a C counter | `mdtests/rb_first_last.md` and `examples/modeled-binary-tree` carry a subtree measure. |
| Ascend through a recursive context | `mdtests/loop_ascending_walk_to_root.md`, `rb_ascending_walk_to_root.md`, and `rb_ascending_walk_in_entry_match.md` carry a context measure while rebuilding the focused tree. |
| Continue after consuming context layers | `mdtests/loop_body_continue_structural_measure.md` checks the explicit `continue` join; `loop_decreases_strict_descendant.md` checks one- and two-layer descent. These are component regressions, not completed rebalancing proofs. |
| Reject staying put | `mdtests/loop_decreases_rejects_same_instance.md` reaches the descent refusal. |
| Reject an unrelated node | `mdtests/loop_decreases_rejects_unrelated_node.md` rejects the missing owned instance at the rebound cursor; it is an ownership/binder regression, not an isolated test of the ancestry comparison. |
| Reject recreating a consumed layer | The audit adds `mdtests/loop_decreases_rejects_rebuilt_layer.md`: unfold the recursive layer, refold it under a fresh name with the same model, then close the back edge. Folding succeeds and descent is refused. Removing only the decreases clause verifies the same proof, isolating the ranking failure. |

The remaining integration acceptance is unchanged C with a checked measure on
**every continuing back edge** of the required algorithms. In C3a the
recolouring `continue` must return `up.up` with all invariants; C3b's rotation
`break` paths must establish their exit guarantees and do not need descent
across an edge that exits. C4b must finish the actual `rb_next`/`rb_prev`
descent/ascent paths, and C5 must cover erase/rebalancing, including any
rotation followed by a continuing edge in the unchanged source. The synthetic
component tests do not substitute for those algorithm proofs. Do not add a C
counter, bounded unrolling, a heap-size assumption, or a rewritten control-flow
path to satisfy termination.

There is no separately demonstrated missing structural-ranking operation to
implement next. Resume the corresponding rbtree proof package and reduce any
new kernel obstruction it exposes. Preserve the same-instance, unrelated-node,
and rebuilt-layer negatives. Concurrent-reader termination, general recursion
extensions, and broader well-founded resource families remain outside this
sequential MVR obligation; see [recursion.md](recursion.md).

Audit validation: all four `loop_decreases` fixtures pass under ordinary and
candidate stable-loan semantics. Ordinary `click audit` checks all five smart
sites in `loop_decreases_strict_descendant.md` and all four in
`loop_body_continue_structural_measure.md`. The rebuilt-layer negative reaches
the descent refusal; its control without the measure verifies. The full unpiped
`scripts/check.sh` passes, including the existing traversal/ascent fixtures and
the new negative. This is an evidence audit of the stated milestone, not an
exhaustive soundness or scaling audit of the resource kernel.

The maintained language explanation is
[structural loop measures](../docs/concepts/loops-and-invariants.md#structural-loop-measures).

## Acceptance criteria

- Preserve the implemented ownership-backed resource fields and compositional
  parent/child models; no generalized witness syntax is required by itself.
- Models retain pointer identity without turning pointers into arithmetic
  integers or granting pointee ownership.
- Function contracts can relate entry and exit models across a changed root.
- Loops carry named modeled instances (D5) and structural measures (D6);
  matched instances expose their selected arm at contract lowering and loop
  heads (D7); matched arms own children of other declared resources (D8).
- Reasoning and certificates are output-sensitive in the explicitly exposed
  model terms; no tactic unfolds an unknown whole tree automatically.
- Required rbtree contracts establish exact rotation order preservation,
  insertion of the designated node, erasure of the designated node, and the
  specified identity substitution on replacement. Insertion and erasure
  describe the correct sequence change, not equality with the input sequence.
- Models express parent/child consistency, acyclicity, red-black color and
  black-height invariants, and correct traversal results. Required algorithms
  establish their respective guarantees, including structural termination on
  all continuing back edges as recorded in the audit above.
- Small positive and negative rotation and insert/erase regressions (synthetic
  or on the pinned source), required MVR model proofs, and
  `scripts/check.sh` pass.

Integer specification coverage is landed and documented in
[the mathematical-integer internals](../docs/internals/mathematical-integers.md);
this MVR model work has no pending dependency on the retired Integer P1
issue. Related: [algebraic-data-types.md](algebraic-data-types.md) and
[recursion.md](recursion.md).
