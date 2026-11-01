# rbtree-augmented's sized resources lack #1245's parent pointer fact

Soundness: incomplete. Existing checked proofs are refused; nothing false is
accepted.

#1245 (`2cee79c02`, pointer designation) added
`fact ((p->__rb_parent_color & ~3) as (struct rb_node *)) == parent;` to `rb_at`
and `ctx_at` in `examples/rbtree/rbtree-model`, and made numeric word facts such as
`(old(*p) & ~3) == parent as uint64` stop implying the pointer equality. The
parallel resources in `examples/rbtree/rbtree-augmented` (`sized_at` and the sized
context resources) never received the fact, so every fold of `rb_at` from a
sized node and every loop invariant stated as a pointer equality now fails.
These sidecars verified before #1245; rbtree-augmented is quarantined from
the gate (`tests/examples.rs`), so the merge queue did not run them.

On master `a69f1cff2`:

```sh
cargo build --release --bin click
target/release/click verify examples/rbtree/rbtree-augmented/rbtree_size_metadata.click
```

```text
fold requires the instance body facts for the proposed fields
fact 6 of 9 of arm `Node` is not established
tactic@82:
  let structure = fold(rb_at(p), { model: RbTree::Node(identity, parent, color, ...) }, ...
required body fact: <pointer A> == parent
```

The insert loop sidecars fail at loop entry:

```text
loop 0 invariant 1 entry, owing `((uint64)...) == ((uint64)...) implies parent == parent`
```

Affected: `rbtree_size_metadata`, `rbtree_size_rotate_set_parents`, and the
13 loop sidecars `rbtree_size_insert_{black_parent,color_flip,
context_color_flip,context_double_rotation,context_rotation,context_stop,
double_rotation,mirrored_color_flip,mirrored_context_color_flip,
mirrored_context_double_rotation,mirrored_context_rotation,
mirrored_double_rotation,mirrored_rotation,rotation}.click`.
`rbtree_size_change_child.click` fails a different body fact
(`old(*<pointer A>) != old(parent->rb_left)`, tactic@94) and is probably the
same cause, unconfirmed.

Acceptance: the sized resources state the parent relationship as `rb_at`
does (contract adaptation, no C change), every listed sidecar verifies, and
`click audit --keep-going --time-limit 90m examples/rbtree/rbtree-augmented` has no
new failures. Consider moving one fast sidecar such as
`rbtree_size_metadata.click` into the gate so a kernel change like #1245
cannot break this directory unseen.

## Three sidecars after resource-argument view matching

Resource-argument identity now ignores the view a cast selects, so
`compute_size(old, 0)` accepts a held `size_metadata(rb_old)`. The sidecars
stopped by that refusal moved to later proof obligations.
Rotation and leaf-propagation checks were made against `1044b6034` plus
their proof repairs; ancestor propagation was rechecked on `ded997547` plus
the repair below:

- `rbtree_size_rotate.click` now verifies both the callback and its contract
  theorem. The proof stops immediately before the metadata copy, states the
  source/target separation, and transports the source value and child
  inequalities across that store. It then states the `container_of` alias and
  the child inequalities in the C local's spelling required by `compute_size`.
  The C and contracts are unchanged. All 18 smart sites pass expansion audit.
- `rbtree_size_propagate_tree.click` now verifies both proofs. It cites the
  available parent equality with `assumption()`, transports the explicitly
  typed packed-parent read across the read-only `rb_parent` helper, and
  extracts the loop-exit disjunction before matching and unfolding the walk
  changes its model spelling. C, contracts, and verifier are unchanged.
- `rbtree_size_propagate.click` now verifies. After the `container_of`
  expansion, its proof states that the C local denotes the original node and
  uses that equality with the unfolded leaf facts to establish both null-child
  guards in the local's spelling. The C, contracts, and verifier are unchanged.

`rbtree_size_metadata.click` also verifies both selected proofs. The sized
resources already state the parent-pointer facts described above. Keep this
report open: the remaining sidecars and full-directory audit have not met the
acceptance criteria.

## Rotation helper parent designation

`rbtree_size_rotate_set_parents.click` now verifies both selected proofs. Its
contract requires the explicit masked parent-pointer equality, matching the
ordinary rbtree helper: equality of the packed numeric word does not establish
pointer designation. The non-root proof branches rewrite that premise through
`sized_context_parent` before reading the C local `parent`. All 22 smart sites
pass expansion audit. The C and postconditions are unchanged.

The 14 direct rotation callers retain the typed parent-pointer fact across the
child-link updates and, for double rotations, the inner rotation callback. They
then rewrite the context parent explicitly to supply the helper's premise.
Paired runs of all 14 callers on `e7cb3ca08` and with this repair reach the
same existing failing statements and goals; none fails earlier. The broader
report remains open: the complete insertion sidecars and directory audit do
not yet pass.

## Color-flip insertion

`rbtree_size_insert_color_flip.click` now gets past its first `unfold(state)`
at line 106. A held resource's constructor-valued facts retain nominal pointer
domains, matching the existing handling of typed logical calls. The reduced
`held_resource_constructor_pointer_domain.md` proof unfolds and refolds the
same model successfully, and its expansion audit passes.

The remaining color-flip proof now explicitly frames the root pointer and all
six child links across the three color-word stores. It names the C locals'
node aliases, retains the grandparent's typed null-parent fact across the two
child recolorings, and states the resulting `parent == 0` before recoloring
the root. All three selected proofs in `rbtree_size_insert_color_flip.click`
verify, with the C, contracts, resources, and verifier unchanged by this proof
repair.

The mirrored color-flip sidecar now uses the same explicit framing for the
opposite insertion branch, taking its snapshot after the extra left-child
read. All three selected proofs in
`rbtree_size_insert_mirrored_color_flip.click` verify as well. Its C, contracts,
resources, and verifier are unchanged by this repair. The other sidecars and
full-directory audit still leave this broader report open.
