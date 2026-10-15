# rbtree-erase's `flips_red_all` proof no longer verifies

`examples/rbtree-erase/rbtree_erase_color_flips_red_all.click` fails on
master `765ede188`. A `have` in the outer loop's preservation proof is
refused:

```sh
cargo build --release --bin click
target/release/click verify examples/rbtree-erase/rbtree_erase_color_flips_red_all.click
```

```text
`____rb_erase_color.contract` tactic 10 (`loop`), `preserve` tactic 66:
`have` failed for `sid->rb_right == at(inner_inputs, sid->rb_right)`:
... `simp` failed ...: could not establish
`sid->rb_right == at(inner_inputs, sid->rb_right)`
  this read may have changed since the snapshot the other side reads: the
  memory-history check could not establish that an intervening store is
  separate from this read.
```

The whole example project is nightly-only, so the gate did not catch this.
`click audit examples/rbtree-erase` reports this file as a session failure for
the same refusal, on master `26caef84b`.
Four nightly refusal tests that run this sidecar now fail with the same
unexpected refusal instead of their intended one:

- `rbtree_erase_color_general_flips_red_exit_left_requires_parent_link`
- `rbtree_erase_color_general_flips_red_exit_left_requires_sibling_link`
- `rbtree_erase_color_general_outer_left_requires_sibling_child_link`
- `rbtree_erase_color_general_red_sibling_left_requires_sibling_link`

The proof verified with master `7efa75c47` plus #1061's changes, and #1061
is on `765ede188`. So the break is in another commit between the two.
Which one is not yet known.

Acceptance: the sidecar verifies unchanged (the C is fixed), the four tests
above refuse for their intended reasons, and `example_projects` passes under
`CLICK_NIGHTLY=1`.
