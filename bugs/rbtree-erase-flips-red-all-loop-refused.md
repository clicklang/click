# rbtree-erase `flips_red_all` is refused after its loop

Soundness: not soundness. A previously verifying proof is refused; nothing
false is accepted.

`examples/rbtree/rbtree-erase/rbtree_erase_color_flips_red_all.click` verified on
master at 6bd0854ca (2026-10-17). The C source is unchanged since, so the
change is in the verifier.

Fixed so far:

- #1366's two refusals (typed calls in a loop invariant and in a `match ...
  ensuring` fact on reassigned pointers), and the folded child's object class
  at line 2187 (#1714).
- Stale rewrites at lines 1835, 1940, 2015 and 2177: the verifier now resolves
  `iid->rb_left` to `tmp1` itself, so those `rewrite`s were updated to
  `normalize() using { ... }`.
- Line 1854, `have sid->rb_left == at(inner_inputs, sid->rb_left)`: the cell is
  unchanged across the stores after `mark outer_inputs` only because it is
  separate from `parent->rb_left` and `iid->rb_right`. The proof now states
  those separations and carries the fact with a `transport` from
  `outer_inputs`, as it already does for `parent->rb_right`. A term comparison
  does not frame a cell across stores by itself
  (`docs/internals/verification-efficiency.md`, "Simple means locally
  checkable").
- Line 2249, the `Empty` arm's null child: `unfold(ns)` projected the node's
  cells at `zid`'s alias spelling with fresh load names, beside the copy
  already cached at the owner's spelling, so `sibling->rb_left` and
  `zid->rb_left` read one cell as two values. The unfold now projects at the
  older spelling of a pointer argument
  (`mdtests/an_unfold_through_an_alias_keeps_the_owners_cell_names.md`).

## Remaining: a slow `unfold` (verifier defect)

```sh
cargo build --release --bin click
target/release/click profile examples/rbtree/rbtree-erase/rbtree_erase_color_flips_red_all.click
```

```text
verification budget exhausted inside tactic `unfold`
tactic@2268:
  let { right: cl, left: cr } = unfold(nleft);
```

`unfold` is simple, with a budget of 750,000 units. `unfold(ns)` at line 2247
costs about 500,000 units, and `unfold(nleft)` at line 2268 crosses the budget.
The commit before #1366 (`586cd7e3`) passes line 2268 and stops later, at line
4232, on the loop's control-work budget.

#1808 removed one cause, implicit arm refutation by predicate facts (63,000
to 79,000 units per held `rb_at`), but the refusal stands. Nearly all of the
rest is the unfold's child-instance loop in
`rewrite_resource_instance_selecting_children_unspelled`: evaluating each
child argument (`p->rb_left`, `p->rb_right`) costs 12,000 to 194,000 units,
and composing the child costs about 500. Stack samples of those reads show:

```text
evaluate_c_memory_load_case → memory_dag_cell_source_walk → step_effect::affects
→ CallKeptRanges::range_holding → kept_range_holds_access
→ pointer_element_index_from_base_with_width → decide
→ decide_from_order_rules → has_condition_fact → condition_matches
→ EqualityGraph::are_int32_equal (term interning)
```

The read walks the memory history. At each call step it crosses, it asks
whether the address lies in one of the call's kept ranges, and each of those
membership questions computes an element index through the general
`decide`. Profiler-named spans account for only about 26,000 of the
194,000-unit read. This is in the condition decision and fact store, which
the smart-tactics work (`roadmap/smart-tactics.md`, "Fast-part scans") is
reworking; it was handed to that work on 2026-10-21.

`rbtree-erase` is a nightly example, so the gate does not run it.

## Acceptance criteria

- The command above verifies, with work close to its earlier 28.8 million
  units.
- A reduced scaling regression covers the slow `unfold`.
