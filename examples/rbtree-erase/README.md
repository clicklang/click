# Linux rbtree erase

`rbtree_erase.click` verifies the unchanged Linux `__rb_erase_augmented`
implementation when the erased node is the root and has at most one child.
It covers an empty replacement, a right child, and a left child. The contract
returns the erased node's raw field ownership and a whole `rb_root_at(root)`
whose root is black, whose parent is null, and whose in-order sequence is the
concatenation of the old left and right subtrees. The returned fixup parent is
null: these root cases need no subsequent erase fixup.

This is the first C increment of chunk 11 in
[the rbtree issue](../../issues/rbtree-example.md). Non-root deletion and both
successor-splice branches are still unproved. The C file retains all branches;
the sidecar's preconditions state the current proof coverage explicitly.

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
root-deletion theorems in `rbtree_erase_root.click` independently. Example
regressions pin the source and reject deletion with a skipped parent/color
write or root replacement.
