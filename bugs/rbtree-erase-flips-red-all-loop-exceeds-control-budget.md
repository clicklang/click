# rbtree-erase's `flips_red_all` loop exceeds the control work budget

Soundness: not soundness. The proof is refused for spending more than its
deterministic budget; nothing false is accepted.

`examples/rbtree-erase/rbtree_erase_color_flips_red_all.click` is refused
because the outer `loop` tactic of `____rb_erase_color.contract` spends more
than the 2,500,000-unit control budget:

```sh
cargo build --release --bin click
target/release/click verify examples/rbtree-erase/rbtree_erase_color_flips_red_all.click
```

```text
verification budget exhausted inside tactic `loop` in `____rb_erase_color.contract`
exhausted its deterministic control work budget after 2500004 units
(2500000 limit; statement 5, source tactic 10)
```

With the budget raised locally (`control` in `src/instrumentation.rs`; do not
commit that) the whole sidecar verifies, so this is the only remaining
refusal. Measured loop work, from `CLICK_TIMINGS=1`:

| revision | loop work |
| --- | --- |
| `7efa75c47` | 2,447,984 |
| `357fabf13` (first over budget; merge of `863de60ed`, "Check registered pointer-read prefixes in interior resource lookup") | 2,527,004 |
| `b9287e862` | 2,528,573 |
| master `e6d3b49fb` with the frontier load-equality bridge fix | 2,553,371 |

The loop was already at 98% of its budget before `863de60ed` added about
79,000 units, so any small growth refuses it. By operation, the run's work
is dominated by `instance arm refutations` on `rb_at` (about 1.9 million
units over 537 calls); the largest growth since `7efa75c47` is in
`cell epoch walk`, `canonicalize atomic loads: miss`, and
`composition-owned store separation`. Which of these the `loop` tactic itself
is charged for has not been isolated.

The violated invariant is the work budget: a control tactic should not spend
eight times the next-largest control tactic in the corpus
(`TacticWorkLimits` documentation), and raising the budget is not a fix.

The earlier refusal of this sidecar (a `have` for
`sid->rb_right == at(inner_inputs, sid->rb_right)` at `preserve` tactic 66) is
fixed; `mdtests/loop_node_link_frames_across_parent_link_store.md` covers it.

Acceptance: the sidecar verifies unchanged (the C is fixed) within the
default budgets, the four nightly refusal tests
`rbtree_erase_color_general_flips_red_exit_left_requires_parent_link`,
`rbtree_erase_color_general_flips_red_exit_left_requires_sibling_link`,
`rbtree_erase_color_general_outer_left_requires_sibling_child_link` and
`rbtree_erase_color_general_red_sibling_left_requires_sibling_link` refuse for
their intended reasons, and `example_projects` passes under `CLICK_NIGHTLY=1`.
