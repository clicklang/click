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

These are C increments of chunk 11 in
[the rbtree issue](../../issues/rbtree-example.md). Non-root deletion, deeper
successors, and immediate successors with a replacement child remain. The C
file retains all branches; each sidecar states its
current coverage explicitly.

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
