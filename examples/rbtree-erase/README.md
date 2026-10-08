# Linux rbtree erase

`rbtree_erase.click` verifies the unchanged Linux `__rb_erase_augmented`
implementation when the erased node is the root and has at most one child.
It covers an empty replacement, a right child, and a left child. The contract
returns the erased node's raw field ownership and a whole `rb_root_at(root)`
whose root is black, whose parent is null, and whose in-order sequence is the
concatenation of the old left and right subtrees. The returned fixup parent is
null: these root cases need no subsequent erase fixup.

`rbtree_erase_successor.click` additionally verifies two-child root deletion
when the right child is a red leaf: the immediate-successor branch. It proves
the exact `rb_successor_splice` model, red-black validity, parent consistency,
and the old left/right in-order sequence, with a null fixup parent. Its
contract requires a parent-consistent input tree.

`rbtree_erase_black_successor.click` covers an immediate black-leaf successor
at the root. It returns the successor as a non-null fixup parent, an empty
hole, and the exact `ctx_at` context missing one black level. The context
preserves parent consistency and the remaining in-order sequence. This is
the input to erase-color fixup; it does not claim that the tree is already
red-black.

`rbtree_erase_child_successor.click` covers an immediate successor with a
nonempty replacement child at the root. Blackening the child's root restores
balance without erase-color fixup. The proof returns the exact remaining
model, red-black validity, parent consistency, and the remaining in-order
sequence, with a null fixup parent.

`rbtree_erase_black_leaf.click` covers a black leaf below the root, on either
parent link. It returns the detached node's fields, an empty hole, the unchanged
context model with a one-black-level deficit, and the non-null parent to fix up.
The right-child proof unfolds the sibling so execution can establish that the
left link does not alias the erased node. This sidecar holds and returns exclusive
ownership of the callback table; the root sidecars borrow it with explicit
separation requirements.

`rbtree_erase_red_leaf.click` covers a red leaf below the root on either parent
link. Its unchanged context accepts an empty black hole at the same black
height, so balance is preserved and the fixup return is null. It uses the same
exclusive callback-table contract as the black-leaf sidecar.

`rbtree_erase_right_child.click` and `rbtree_erase_left_child.click` cover
non-root deletion with one nonempty child, for either child direction and either
parent link. Neither contract assumes the erased node's or child's color.
Validity implies that copying the erased node's parent/color word blackens the
child. The proofs return that exact replacement model and the unchanged context,
with whole-tree red-black validity, parent consistency, preserved child in-order
contents, and a null fixup parent. Both use exclusive callback-table ownership.

`rbtree_erase_nonroot_successor.click` extends the immediate red-leaf successor
case below the root, on either parent link. It returns the exact successor
subtree and unchanged outer context, whole-tree balance, parent consistency,
and the old left/right in-order contents, with null fixup. The erased node's
color is not assumed. It holds and returns exclusive callback-table ownership.

`rbtree_erase_nonroot_black_successor.click` covers an immediate black-leaf
successor below the root, on either parent link. It returns that successor as
the non-null fixup parent and the exact context with a one-black-level deficit.
Plugging its empty hole equals the intended successor splice in the original
outer context. Parent consistency is preserved; balance still needs fixup.

These are C increments of chunk 11 in
[the rbtree issue](../../issues/rbtree-example.md). Non-root immediate nonempty-child successors and deeper successors remain. The C file retains all branches; each sidecar
states its current coverage explicitly.

The callback contracts describe the non-augmented case: callbacks cannot
mutate tree fields or require augmentation metadata. The borrowed table is
separated from fields the C may write. Metadata-carrying callbacks remain
chunk 14.

The input is extracted from `include/linux/rbtree_augmented.h` inside
[`input-closure.tar.gz`](../../integrations/linux-rbtree/input-closure.tar.gz).
The `rb_augment_callbacks` declaration and `__rb_erase_augmented` definition,
including comments, are verbatim. The header shim reuses the insertion
example's supported rbtree types and macros and spells the pinned
`__rb_parent` mask. This is not yet the complete pinned translation-unit
integration planned in chunks 21–24. The source is GPL-2.0-or-later.

Run `click verify examples/rbtree-erase` and
`click verify examples/rbtree-model`. The latter checks the imported pure
root-deletion and successor-splice theorems independently. Example regressions
pin the source and reject skipped parent/color writes, root replacement, or
the successor's left-child parent update. The successor's explicit final
claim closers also re-verify. Black-successor mutations reject a skipped root
replacement and incorrectly returning null instead of the fixup parent.

Replacement-child mutations reject a missing parent/color write and a write
that leaves the child red.

Non-root leaf mutations reject an unchanged left or right parent link, a null
fixup return for black leaves, and a non-null fixup return for red leaves.

One-child mutations reject unchanged parent links, missing parent/color writes,
leaving the replacement red, and a non-null fixup return.

Non-root red-successor mutations reject unchanged parent links, missing left
subtree attachment or parent updates, missing successor parent/color writes,
and a non-null fixup return.

Non-root black-successor mutations additionally reject null fixup and incorrectly
returning the erased node's parent instead of the successor.
