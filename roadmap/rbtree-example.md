# Verify the Linux rbtree example on the recursive structure models

Priority: P1.

Soundness: not soundness. This is example delivery. Soundness defects found
along the way were fixed when they were found; none is open against this item.

## Launch claim

Maintainer ruling, 2026-11-24: the launch claim is "Click verifies the Linux
rbtree implementation: `lib/rbtree.c`, the inline helpers from `rbtree.h` and
`rbtree_augmented.h` that it uses, and `rb_link_node`." The source is the
unchanged Linux v6.8.12 input closure pinned in
[`integrations/linux-rbtree/`](../integrations/linux-rbtree/README.md), under
its one recorded compiler profile (`linux-6.8-x86_64-kbuild`, GCC 13.3.0,
x86_64 LP64).

`rb_add`, `rb_find`, and the `*_cached` and other generic header helpers
(`rb_add_cached`, `rb_find_add`, `rb_erase_cached`, and the like) are outside
the launch claim and are post-launch work.

The proof establishes sequential memory safety and defined behavior;
parent/child consistency and acyclicity; preservation of the red-black color
and black-height invariants by insertion and erasure; preservation of the exact
node set and in-order sequence by rotations, insertion, erasure, and
replacement; correct traversal results; termination of finite-tree traversal
and rebalancing loops; and modular correctness for caller-supplied augmentation
callbacks. It checks the sequential store effect of `WRITE_ONCE`, `READ_ONCE`,
and `rcu_assign_pointer`, and claims nothing about concurrent readers, atomic
ordering, RCU grace periods, or data races
([concurrency model](../docs/internals/concurrency-contracts-and-diagnostics.md#remaining-gaps)).
Compiler and target assumptions are described in the
[C ABI documentation](../docs/internals/kernel.md#c-abi-and-memory-layout).

## Where the delivered work is

The models, sidecars, and their current coverage are documented with the code:

- [`examples/rbtree/rbtree-model`](../examples/rbtree/rbtree-model/README.md):
  `RbTree`/`Context` models, `rb_at`/`ctx_at` resources, insert-fixup and
  erase-splice lemmas.
- [`examples/rbtree/rbtree-insert`](../examples/rbtree/rbtree-insert/README.md):
  `__rb_insert` and `rb_insert_color`.
- [`examples/rbtree/rbtree-erase`](../examples/rbtree/rbtree-erase/README.md):
  the general unlink (`rbtree_erase_augmented.click`), the general color
  repair (`rbtree_erase_color_flips_red_all.click`), and `rb_erase`
  (`rbtree_erase_general_wrapper.click`).
- [`examples/rbtree/rbtree-augmented`](../examples/rbtree/rbtree-augmented/README.md):
  the augmented entry points and the concrete subtree-size augmentation.
- `mdtests/rb_first_last.md`, `mdtests/rb_next.md`, `mdtests/rb_prev.md`
  (with `_rejects_a_dropped_context` negatives), `mdtests/rb_replace_node*.md`,
  and `mdtests/rb_parent_family.md` (which contracts a copy of
  `rb_link_node`).
- [`integrations/linux-rbtree`](../integrations/linux-rbtree/README.md): the
  pinned closure, lock, and dependency-closure projection, with its gate tests
  in `src/languages/c/linux_rbtree_tests.rs`.

Chunks 1 to 13 (insertion, `rb_insert_color`, `rb_next`/`rb_prev`, erase) and
15 to 22 (pinned-source importer, dependency-closure projection, the
`linux-6.8-x86_64-kbuild` option profile, committed lock) are landed. Their
history, the settled design decisions D1 to D10, the closed-gap table, and the
structural-termination audit are in
[the previous version of this file](https://github.com/clicklang/click/blob/5da40d716/roadmap/rbtree-example.md)
and in Git history.

## Verification evidence

The sidecars verify verbatim extracts of the pinned C, checked by SHA-256 in
`tests/examples.rs`; the pin tests run in the PR gate. `rbtree/rbtree-model`
verifies in the gate. `rbtree/rbtree-insert`, `rbtree/rbtree-erase`, and
`rbtree/rbtree-augmented` are in the `NIGHTLY` list of `tests/examples.rs`, and
85 of the 90 `rbtree_*` tests there are `#[ignore = "nightly: ..."]`, so the PR
gate does not catch a regression in an insertion, erase, or augmented proof.

The 2026-11-23 nightly run (GitHub Actions run 45233450098) failed 62
`clicklang::examples` rbtree tests: the erase and erase-color mutation tests,
the `rbtree_sized_*` retained-session expansion rechecks,
`rbtree_null_parent_helper_verifies`, `rbtree_rotate_set_parents_*`, and
`rbtree_augmented_wrappers_reject_missing_or_wrong_calls`. Its expansion audit
also failed on `rbtree_erase_color_flips_red_all.click`,
`rbtree_size_propagate_tree.click`, `rbtree_size_callbacks.click`, and most
`rbtree_size_insert_*` sidecars. Repairs landed after that run started (e.g. `9af8bcca`,
`4c2f4624`, `3fc7e385`); no green nightly confirms them yet.

[PR #3476](https://github.com/clicklang/click/pull/3476) and
[PR #3501](https://github.com/clicklang/click/pull/3501) record the last
focused runs of the general erase splice and color repair. The
[earlier focused run](https://github.com/clicklang/click/blob/f25b570397/roadmap/rbtree-example.md#focused-verification-on-current-master)
records the callback-table write refusal that
[smart-tactics.md](smart-tactics.md) cites.

## Violated invariant

Contracts for a mutable recursive structure must relate its finite abstract
model before and after mutation, with the model derived from the owned
structure, and a verified translation unit must include the semantics of the
actual inline bodies its headers supply: no called helper may become opaque
because it came from a header.

## Intended regression

The pinned `lib/rbtree.c` translation unit, imported through
`integrations/linux-rbtree/click.project.json` without changing the upstream
`.c` or headers, verifies against the sidecar contracts for every function in
the launch claim. Rotation, insertion, and erasure mutations that drop a
subtree, reuse a child, skip a parent/color write, or reorder nodes are
refused, as the existing extract-based mutation tests are.

## Open work

A chunk is one pull request with its regressions and docs. C is fixed;
adaptation goes into contracts, lemmas, resources, tactics, lowering, or the
kernel.

**Nightly greenness.** Confirm that the rbtree example tests and the rbtree
expansion-audit sessions pass in a nightly run, and repair what does not, before
building further on them. Consider moving a cheap representative rbtree check
into the PR gate within the ten-minute budget.

### Augmented

**Chunk 14. Writable augmentation callbacks.** The concrete subtree-size
callbacks (`rbtree_size_compute`, `rbtree_size_copy`, `rbtree_size_rotate`,
`rbtree_size_propagate_tree`, packaged in `rbtree_size_callbacks.click`)
verify, and sized insertion verifies the root, black-parent, arbitrary
color-flip chains (`rbtree_size_insert_flip_chain.click`), single rotations,
and double rotations whose focused node's other child and uncle are empty
(`rbtree_size_insert_*context_double_*_rotation.click`). The general
structural entry points still import callback contracts without writable
footprints. Remaining:

- generalized double rotations with arbitrary transferred-middle, focused-child,
  and uncle subtrees (the model theorems exist; the C compositions do not);
- color-flip chains that end in a rotation, giving one general sized insertion
  contract for `__rb_insert_augmented`/`rb_insert_augmented`;
- writable-callback erase integration: `__rb_erase_augmented`,
  `__rb_erase_color`, and `rb_erase_augmented` with propagate/copy/rotate
  writing metadata (today `rbtree_erase_leaf.click` covers leaf deletion
  with non-writing callbacks only).

### Pinned source

**Chunk 23. Proofs over the pinned inline helpers.** Depends on 22, which is
landed. The header-inline mechanism is landed (`static inline` and
`static __always_inline` header definitions get translation-unit-local
linkage, take sidecar contracts, are called through a contract when they have
one and run their body at the call site otherwise, and report `header.h:line`;
`docs/reference/language/c.md`, `mdtests/inline_functions_in_headers.md`,
`mdtests/always_inline_functions_in_headers.md`,
`mdtests/inline_helper_sidecar.md`, `mdtests/inline_header_error_location.md`,
`mdtests/conflicting_inline_helpers_across_headers.md`,
`mdtests/duplicate_inline_helpers_across_headers.md`). The pinned unit
imports: `linux_rbtree_locked_import_loads_offline` parses the projected unit,
which keeps 32 of 2,575 file-scope declarations and defines 26 functions
(`PROJECTED_FUNCTIONS`, `src/languages/c/linux_rbtree_tests.rs:35-62`): the 12
external-linkage definitions in `lib/rbtree.c` plus 14 translation-unit-local
helpers such as `rb_set_parent_color`, `__rb_change_child`,
`__rb_rotate_set_parents`, and `__rb_erase_augmented`. That test is
nightly-only. No proof runs against the imported bodies:
`integrations/linux-rbtree/rbtree.click` is the single line
`verifying "inputs/lib/rbtree.c";`. Remaining:

- Contracts and proofs for every projected function, run on the imported
  bodies. Several have no proof even as an extract: `rb_first_postorder`,
  `rb_next_postorder`, `rb_left_deepest_node`, and `rb_replace_node_rcu`.
  `mdtests/rb_next.md` still declares `rb_next`'s parameter without `const`
  (`mdtests/rb_next_const_signature.md`); the pinned signature has it.
- `rb_link_node`. It is in the artifact (`include/linux/rbtree.h:59`) but
  `lib/rbtree.c` never calls it, so the projection omits it: projection roots
  are function definitions in the unit's primary source file
  (`src/languages/c/projection.rs`). Including it needs a general way to
  select a header-defined inline function as an additional projection root
  (or another checked route to the same pinned body), then its contract and
  proof; `mdtests/rb_parent_family.md` has a contract for a copy.
- Every helper the claim covers is verified from its body or named as an
  explicit external trust boundary; none is opaque because it came from a
  header. `extern inline`, richer inline signatures, and broader GNU alignment
  forms stay explicitly refused, not silently accepted.

**Chunk 24. Attach the sidecars to the pinned translation unit** and replace
the verbatim-extract fixtures and their SHA-256 pins with the pinned
regression. Depends on 14 and 23.

## Acceptance criteria

- Models retain pointer identity without turning pointers into integers or
  granting pointee ownership; contracts relate entry and exit models across a
  changed root; reasoning is output-sensitive in the exposed model terms.
- Rbtree contracts establish exact rotation order preservation, insertion of
  the designated node, erasure of the designated node, and the specified
  identity substitution on replacement, describing the correct sequence change.
- Models express parent/child consistency, acyclicity, red-black color and
  black-height invariants, and correct traversal results; every continuing
  back edge has a structural termination measure.
- Every function in the launch claim verifies on the imported pinned unit with
  original file and line attribution and unchanged linkage identity; fixture
  provisioning follows [the pinned preprocessing inventory](../design/kernel-preprocessing-inventory.md)
  (no downloads in the gate, no silent skips).
- Positive and negative rotation and insert/erase regressions, the rbtree
  nightly example tests and expansion audit, and `scripts/check.sh` pass.
