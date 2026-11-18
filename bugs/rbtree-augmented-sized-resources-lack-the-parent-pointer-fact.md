# rbtree-augmented's sized resources lack #1245's parent pointer fact

Soundness: incomplete. Existing checked proofs are refused; nothing false is
accepted.

#1245 (`2cee79c02`, pointer provenance) added
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
  available parent equality with `known()`, transports the explicitly
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

## Rotation helper parent provenance

`rbtree_size_rotate_set_parents.click` now verifies both selected proofs. Its
contract requires the explicit masked parent-pointer equality, matching the
ordinary rbtree helper: equality of the packed numeric word does not establish
pointer provenance. The non-root proof branches rewrite that premise through
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
opposite insertion branch, taking its state after the extra left-child
read. All three selected proofs in
`rbtree_size_insert_mirrored_color_flip.click` verify as well. Its C, contracts,
resources, and verifier are unchanged by this repair. The other sidecars and
full-directory audit still leave this broader report open.

## Root rotation

All three selected proofs in `rbtree_size_insert_rotation.click` now verify.
The proof carries the newly null left child across the following child-link
store and parent-update helper, and frames the unchanged right child and
promoted node's left link across the rotation. The saved old left-child alias
identifies the helper's write target. Empty child resources use the established
null pointer directly, and the promoted root's typed null-parent equality is
rewritten from its tag value of one before folding the rotated tree.

The mirrored right-right root rotation now has the corresponding explicit
framing, with left and right exchanged and the old right-child alias identifying
the parent. All three selected proofs in
`rbtree_size_insert_mirrored_rotation.click` verify too.

These repairs leave the C, contracts, resources, and verifier unchanged. The
other insertion sidecars and full-directory audit still leave this report open.

## Double rotation

All three selected proofs in `rbtree_size_insert_double_rotation.click` now
verify. The inner rotation explicitly preserves the unchanged right child and
parent/color word, including the typed parent relationship, and carries the
new left-child link across the parent-color store. The outer rotation carries
its newly null child across the following link store and parent-update helper,
preserves the promoted node's left child, and states its typed null-parent
relationship before refolding. Empty outer children use the established null
pointer directly.

Both rotation callbacks remain in the proof. This repairs the left-right
three-node insertion without changing the C, contracts, resources, or verifier.
The mirrored double rotation, remaining context sidecars, and directory-wide
audit are still outside this completed repair; keep the broader report open.

## Mirrored double rotation

All four selected proofs in `rbtree_size_insert_mirrored_double_rotation.click`
now verify, including a root-case contract for `__rb_rotate_set_parents`.
The insertion proof also expands and rechecks in the retained verification
session. The C and the three original insertion contracts are unchanged.

Small owned resources retain the complete parent-word relationships and the
unchanged right link across writes. Opening and immediately refolding the
right subtree exposes its node identity before retaining that link. The root
helper contract proves both updated parent words and the root link separately;
explicit color bounds retain the pointer representation through the tagged
store. The outer proof uses those postconditions and states the promoted
root's typed null-parent relationship before folding.

This is a proof repair, with no verifier change. The remaining context sidecars
and directory-wide audit still leave the broader report open.

## Context color flip and black-parent stop

All three selected proofs in `rbtree_size_insert_context_color_flip.click`
now verify. The proof retains the root pointer and all six child links in an
owned frame across the recolorings. It retains the grandparent's parent word
until the parent read, then retains each newly black parent word across the
remaining stores before refolding the subtrees. The C and original contracts
are unchanged; this part is a proof repair.

The grouped insertion proof's expansion exposed a separate serialization bug:
a back-edge certificate split into guarded conjunction members still printed
the retired `close_invariants` syntax. Expansion now emits those members as
ordered `have` proofs, preserving each member's body and the dependencies on
earlier members. The expanded source rechecks.

`rbtree_size_insert_context_stop.click` already verifies all three selected
proofs on `2bab9ff83`, without changes.

The mirrored context color flip now also verifies all three selected proofs.
It uses the same owned frames across its recoloring calls, with the frame
definitions shared by both sidecars in `rbtree_size_context_flip_frames.click`.
Its C and contracts are unchanged, and the insertion proof expands and rechecks.
Other remaining sidecars and the directory-wide audit still leave this report open.

## Context rotation

All three selected proofs in
`rbtree_size_insert_context_rotation.click` now verify. The proof retains
ancestor links and complete tagged-parent relationships across local
initialization and read-only steps, executes the missing declaration and
middle-child store, and keeps unchanged and newly written links in owned
resources through the rotation helper. Empty children are refolded at the
established null pointer.

The shared `rbtree_size_rotate_set_parents.click` helper now also guarantees
the promoted node's typed parent relationship, in addition to the copied
numeric parent word. Its proof retains that complete relationship across the
ancestor-link update. The output link uses the entry value of the unchanged
subtree count; the existing unchanged-size guarantee is retained. Both helper
proofs verify. Expansion audits pass all 10 sites in the insertion sidecar
and all 34 sites in the shared helper.

The C, original insertion contracts, existing tree-resource definitions, and
verifier are unchanged by this repair. Other context sidecars and the
full-directory audit remain outside this completed repair; keep this report
open.

## Mirrored context rotation

All three selected proofs in
`rbtree_size_insert_mirrored_context_rotation.click` now verify at default
limits. The right-right rotation retains ancestor links and complete tagged-parent
relationships across initialization and read-only steps, explicitly executes the
local declaration and middle-child store, and retains unchanged and newly written
child links through the parent-update helper. Empty children are refolded at the
established null pointer.

Expansion, cold-replay, and fixed-point checks pass all 10 audit sites across
the insertion and its two wrappers. This mirrors the completed context-rotation
repair. The C, original insertion
contracts, existing tree-resource definitions, and verifier are unchanged. The
remaining context sidecars and full-directory audit still leave this report open.

## Context double rotation

All three selected proofs in
`rbtree_size_insert_context_double_rotation.click` now verify at default
limits. The left-right rotation under an ancestor retains complete node
observations across initialization and reads, executes the missing `tmp`
declaration and inner-pivot load, and retains unchanged tags and child links
through both rotations and the first callback. Opening and refolding the
first callback's child exposes its identity before retaining that link through
the outer parent update. Distinctness of the grandparent and pivot is stated
explicitly from ownership of their separate header cells.

Expansion, cold-replay, and fixed-point checks pass all 13 audit sites across
the insertion and its two wrappers on merged master `262fd90d1`.

Both callbacks, the C, the three original function contracts, existing tree
resources, and verifier are unchanged. The remaining sidecars and full-directory
audit still leave this report open.

## Mirrored context double rotation

All three selected proofs in
`rbtree_size_insert_mirrored_context_double_rotation.click` now verify at
default limits. The right-left case retains complete parent tags and child
links across initialization, the extra mirrored uncle read, both rotations,
and their callbacks. It executes the missing local declaration and pivot
load, exposes the first callback child's identity before retaining the link,
and proves grandparent/pivot distinctness from separate owned header cells.
The final fold's count equation is stated directly in the library's child order.

Expansion, cold-replay, and fixed-point checks pass all 13 audit sites across
the insertion and its two wrappers on merged master `d6e2b0979`.

The C, three original function contracts, both callbacks, existing tree
resources, and verifier are unchanged by this proof repair. Other sidecars
and the full-directory audit still leave this report open.

## Context double rotation with an arbitrary far subtree

All four selected proofs in
`rbtree_size_insert_context_double_far_rotation.click` now verify at default
limits, including the inorder-preservation theorem and both insertion wrappers.
The far subtree and its cached count remain arbitrary. The proof retains its
owned resource and incoming link through the rotations, alongside complete
parent tags and the other unchanged child links. It explicitly executes the
local declaration and pivot load, refolds empty children at null, and exposes
the first callback child's identity before retaining that link through the
outer parent update. The existing count and overflow arguments are retained.

Expansion, cold-replay, and fixed-point checks pass all 30 audit sites on
merged master `857116880`.

The C, original contracts and theorem, both callbacks, existing tree resources,
and verifier are unchanged by this repair. Other sidecars and the full-directory
audit still leave this report open.

## Mirrored context double rotation with an arbitrary far subtree

All four selected proofs in
`rbtree_size_insert_mirrored_context_double_far_rotation.click` now verify at
default limits on master `ce6511723` plus the proof repair, including the
inorder-preservation theorem and both insertion wrappers. The right-left case
retains complete node observations across initialization and reads, executes
the missing local declaration and pivot load, and retains parent tags and
child links through both rotations and callbacks. Empty children are refolded
at null, and the first callback child's identity is exposed before retaining
its link through the outer parent update. The far subtree and its valid cached
count remain arbitrary; the original mirrored count arguments are retained.

Expansion, retained and cold verification, and fixed-point checks pass all 30
audit sites on merged master `ce6511723` plus this proof repair, at default
limits.

The C, three original function contracts, inorder theorem, both callbacks,
existing tree resources, and verifier are unchanged. Other sidecars and the
full-directory audit still leave this report open.

## Context double rotation with a nonempty transferred subtree

All four selected proofs in
`rbtree_size_insert_context_double_middle_subtree_rotation.click` now verify
at default limits on master `7b90f7357` plus the proof repair, including the
inorder-preservation theorem and both insertion wrappers. Initialization
exposes the transferred root's entry-time identity and retains complete node
observations through the C reads. The proof executes the missing local
declaration and pivot load, retains tags and child links through the inner
rotation and parent updates, and reparents the nonempty middle subtree with
its original arbitrary children and cached count. Both writable callbacks
and the original count arguments remain in the proof. The outer rotation
retains the first callback child's identity and restores the ancestor context.

Expansion, retained and cold verification, and fixed-point checks pass all 21
audit sites at default limits.

The C, three original function contracts, inorder theorem, tree models,
callbacks, existing tree resources, and verifier are unchanged. Other sidecars
and the full-directory audit still leave this report open.

## Mirrored context double rotation with a nonempty transferred subtree

All four selected proofs in
`rbtree_size_insert_mirrored_context_double_middle_subtree_rotation.click`
now verify at default limits on master `1aeae5459` plus the proof repair,
including the inorder-preservation theorem and both insertion wrappers.
Initialization retains the transferred root's entry-time identity and complete
node observations through the C reads. The right-left rotation explicitly
executes the missing local declaration and pivot load after the mirrored uncle
read, retains tags and child links through both parent updates, and reparents
the transferred subtree with its original arbitrary children and cached count.
Both writable callbacks and the existing mirrored count arguments remain.
The outer rotation retains the first callback child's identity and restores
the ancestor context.

Expansion, retained and cold verification, and fixed-point checks pass all 27
audit sites at default limits.

The C, three original function contracts, inorder theorem, tree models,
callbacks, existing tree resources, and verifier are unchanged. Other sidecars
and the full-directory audit still leave this report open.

## Context rotation with a nonempty black middle leaf

All three selected proofs in
`rbtree_size_insert_context_middle_rotation.click` now verify at default
limits on master `81adf013b` plus the proof repair, including both insertion
wrappers. Complete node observations retain the child inequalities and typed
parent relationships through initialization and read-only loop steps. The
proof executes the missing local declaration and middle-child store, retains
the unchanged and newly written child links through both parent-update calls,
and reparents the black middle leaf before restoring the ancestor context.
The callback count equation closes explicitly from `gv == 3 + nv`. Arbitrary
focused-node subtrees, symbolic valid cached sizes, and the writable size
callback remain in the proof.

Expansion, retained and cold verification, and fixed-point checks pass all 13
audit sites at default limits.

The C, three original function contracts, tree models, imported inorder
theorem, callback, existing tree resources, and verifier are unchanged. Other
sidecars and the full-directory audit still leave this report open.

## Context rotation with an arbitrary nonempty black middle subtree

All three selected proofs in
`rbtree_size_insert_context_middle_subtree_rotation.click` now verify at
default limits on master `0e8e9cd9c` plus the proof repair, including both
insertion wrappers. Complete node observations retain the child inequalities
and typed parent relationships through initialization and read-only loop
steps. The proof explicitly executes the missing local declaration and
middle-child store, retains unchanged and newly written child links through
the transferred subtree's reparenting and the outer parent update, and
restores the ancestor context after the writable callback. Both the focused
and transferred subtrees retain arbitrary owned children and symbolic valid
cached sizes. The original count and overflow arguments remain in the proof.

Expansion, retained and cold verification, and fixed-point checks pass all 23
audit sites at default limits after the obligation fix below. Both targeted
regressions and all 1,857 selected scaling tests pass.

The C, three original function contracts, tree models, imported inorder
theorem, callback, and existing tree resources are unchanged. Other sidecars
and the full-directory audit still leave this report open.

The expansion audit also exposed duplicate written call obligations: closed
comparisons such as `0 <= 0` and `0 <= 1` were distinct when collected but
matched the same obligation on replay. Requirement deduplication now uses
the same canonical comparison as replay. A reduced bounded-argument call
checks expansion and replay with the implicit closer off, and refuses an
argument that violates its upper bound.

## Context rotation with arbitrary focused child subtrees

All four selected proofs in
`rbtree_size_insert_context_focus_rotation.click` now verify at default limits,
including both insertion wrappers and the inorder-preservation theorem. Owned
node observations retain the parent tags, child identities and inequalities
through initialization and the loop's read-only prefix. The proof executes the
missing local declaration and first rotation store, retains the unchanged and
newly written links across the parent-update call, and explicitly normalizes
the callback's count equation from `to_integer(gv) == 2 + to_integer(nv)`.

Expansion, retained and cold verification, and fixed-point checks pass all 13
audit sites at default limits.

The focused node's child subtrees and valid cached sizes remain arbitrary.
The C, three original function contracts, inorder theorem, writable callback,
existing tree resources, and verifier are unchanged. Other sidecars and the
full-directory audit still leave this report open.

## Mirrored context rotation with arbitrary focused child subtrees

All four selected proofs in
`rbtree_size_insert_mirrored_context_focus_rotation.click` verify at default
limits. The proof retains the node observations through the read-only steps,
executes the local declaration and the first rotation store, and carries the
child links through the parent update. The callback count equation uses the
existing `to_integer(gv) == 2 + to_integer(nv)` premise.

The focused subtrees and cached sizes remain arbitrary under the original
contracts. The other sidecars and the full-directory audit remain open.

All 12 expansion, retained and cold replay, and fixed-point audit sites pass
at default limits on master `ecd9cba40` plus this repair.

## Context rotation with nonempty black middle and uncle subtrees

All three proofs in `rbtree_size_insert_context_uncle_rotation.click` verify
at default limits on master `58b0c2c9e` plus the proof repair. The proof carries
the parent and child observations through initialization and the black-uncle
test. It executes the local declaration and both rotation stores, retains
the new child links through the middle subtree's reparenting and the parent
update, and carries the original uncle subtree into the rotated tree. The
original contracts keep the subtrees and their valid cached sizes arbitrary.

## Insertion exit at a black parent

The proof in `rbtree_size_insert_black_parent.click` binds the packed parent
tag at each unfold, then retains the ancestor's word and black bit in an
owned resource across the reads. Refolding uses the saved tags and the
proof executes the remaining local declaration before entering the loop.

## Replacing a child link

The augmented `__rb_change_child` proof retains the ancestor's packed tag and
its typed parent cast, the sibling and root links, and the replaced child's
cached size and parent cast across the store. The produced link uses the
entry size, which the contract separately proves equals the exit size.

## Stopping after insertion color flips

All three proofs in `rbtree_size_insert_flip_boundary.click` verify at
default limits. The proof retains the focus node's typed parent and child
links through initialization, then carries the root link through the
recolor-to-black and black-parent exits. The stopping contracts return the
tree at the entry root pointer and prove that the root pointer is unchanged.
The arbitrary-length flip-chain proof and full-directory audit remain open.
