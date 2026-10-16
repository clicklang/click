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
exhausted its deterministic control work budget after 2500003 units
(2500000 limit; statement 5, source tactic 10)
```

With the budget raised locally (`control` in `src/instrumentation.rs`; do not
commit that) the whole sidecar verifies, so this is the only remaining
refusal. The loop spends 2,636,726 units. A control tactic's own work
includes the structural proof inside it (`match`, proof `if`, interface
joins) but not its nested tactics, so these units are the loop's
bookkeeping, not its `have`s and `step`s.

The violated invariant is the work budget: a control tactic should not spend
eight times the next-largest control tactic in the corpus
(`TacticWorkLimits` documentation), and raising the budget is not a fix.

## Attribution

Work-sampled backtraces of the loop tactic's own work (one sample per 5,000
units, 527 samples) put it in three places, each roughly a quarter to a
third of the total:

- **The exit join, about 800,000 units.** `join_loop_exits` builds a fact
  context for each of the 14 exits from that exit's 113 to 311 facts
  (`loop_exit_argument_contexts`, about 380,000 units, 100 to 160 units per
  fact), restates every exit fact about the merged binders (`restate`, about
  220,000), and re-evaluates each binder's declared arguments per exit
  (about 145,000). The exits share no fact prefix, so a shared prefix context
  would not help; the contexts the proof already built at each exit are
  discarded and rebuilt from the fact lists.
- **Arm refutation at proof `match` case splits, about 700,000 units over 42
  splits.** `algebraic_case_partition` calls `instance_arm_model_facts` for
  the scrutinee's `rb_at`/`ctx_at` instance. A call costs 12,000 units beside
  59 path facts and 28,000 to 34,000 beside 155 to 210, and most publish
  nothing. About half is `arm_is_refuted_by_a_predicate_fact` deciding each
  model premise at the arm's constructor: `decide` reaches the order rules'
  scanned fallback (`condition_matches` over facts whose sides are loads),
  which is linear in the path's facts per decision.
- **Interface joins at proof `match` groups, about 900,000 units.** About
  415,000 is `memory_diff_is_covered_by_ranges` replaying each arm's
  certified call-effect summary through `matches_call_memory_havoc_result`;
  of that, about 365,000 is `kept_range_via_address_class` proving
  `kept_range_holds_access` for candidate ranges, again through `decide`.
  That replay re-derives the call's havoc result that the same session's call
  rule produced. The rest is fixed-state lowering contexts and the joined
  abstraction.

The loop head computes its invariant premise context and refutes every held
instance's arms five times (`with_selected_arm_views` twice,
`with_selected_arm_views_attached` three times, all at the same premise
state); about 100,000 units.

## Fixed so far

- A proof `if` in a preservation region rebuilt a fact context from the whole
  branch fact list for each arm (about 185,000 units here); it now lowers
  against the branch's indexed context
  (`proof_if_split_ignores_earlier_unrelated_facts`).
- Loop-exit cache reconciliation rebuilt the exit contexts the join had just
  built (about 134,000 units); it now reuses them
  (`exit_cache_reconciliation_reuses_the_joins_exit_contexts`).
- Since `d8707aa46` the sidecar had stopped earlier, at a `simp` at line 2355:
  a store forgot cells of its own object whenever a C pointer comparison
  named that object's address. `098f48f35` fixed that; the sidecar again
  stops only at the loop budget.
- Since `215e2c358` the loop's back edge refused `parent`, which
  `rb_parent` returns unclassed while the head keeps the parameter's
  `struct rb_node` class ("loop state join changes pointer object classes"
  at the `close_invariants()` on line 1553). The back edge now keeps the
  head's class for an unclassed pointer
  (`a_loop_may_return_a_struct_pointer_unclassed_from_its_tag_bits.md`);
  the sidecar again stops only at the loop budget.

## Proposed remaining work (needs a design decision)

- Carry each exit's checked fact context to the exit join instead of
  rebuilding it from the exit's fact list.
- Decide arm refutation's model premises against the arm's own premises and
  the facts connected to the instance, rather than through `decide` over the
  whole path context; or index the order rules' load-sided fallback.
- Retire the interface join's replay of certified call-effect summaries
  ("construction, not re-validation"), as stores already do through
  `certified_store_data`.
- Compute the loop head's premise context and arm decisions once.

Acceptance: the sidecar verifies unchanged (the C is fixed) within the
default budgets, the four nightly refusal tests
`rbtree_erase_color_general_flips_red_exit_left_requires_parent_link`,
`rbtree_erase_color_general_flips_red_exit_left_requires_sibling_link`,
`rbtree_erase_color_general_outer_left_requires_sibling_child_link` and
`rbtree_erase_color_general_red_sibling_left_requires_sibling_link` refuse for
their intended reasons, and `example_projects` passes under `CLICK_NIGHTLY=1`.
