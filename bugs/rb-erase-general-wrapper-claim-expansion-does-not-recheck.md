# rb_erase's general-wrapper claim expansion does not recheck

Soundness: not soundness. A verified proof's whole-claim expansion is refused
when it is checked, and nothing false is accepted.

`examples/rbtree-erase/rbtree_erase_general_wrapper.click` verifies, but its
`rb_erase.contract` claim expansion does not:

```sh
cargo build --release --bin click
target/release/click expand --claim rb_erase.contract \
    examples/rbtree-erase/rbtree_erase_general_wrapper.click --output /tmp/out.click
```

```text
click: expanded proof did not verify: `rb_erase.contract` proof step tactic 18:
could not lower `have` proposition: the kernel lowering stopped at no single
evaluation path
  recent premises (showing 8 of 27):
    AugmentRotate(at(<state A>, dummy_callbacks#file-static:rb_erase.c+16))
    EraseCopy(at(<state A>, dummy_callbacks#file-static:rb_erase.c+8))
    ...
```

`click audit examples/rbtree-erase` reports the same claim failure (claim
44/50). It reproduces on master `26caef84b` with the
`claude/nightly-fixes-20261015-b` test-only changes; the claim checks no
source those changes touch. The leaf wrapper's
`rb_erase.contract` (`rbtree_erase_leaf_wrapper.click`), which follows the
same pattern, expands and rechecks. The written proof applies the dummy
callbacks' contracts and folds `erase_callbacks(&dummy_callbacks)`. The
premises name the file-static `dummy_callbacks` by an internal spelling, so
the expanded `have` that fails to lower may print a value through that
spelling. That cause is suspected, not confirmed.

Acceptance:

- `click expand --claim rb_erase.contract` on this file writes a proof that
  verifies with the implicit `auto` off, and the audit of
  `examples/rbtree-erase` passes this claim.
