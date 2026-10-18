# Retained rbtree transport exceeds the simple work budget

Soundness: not soundness. This is a deterministic performance discrepancy:
the original proof and its fully expanded form verify cold, but the audit's
retained-session check exceeds a simple tactic's work budget. No false
acceptance is known.

The next augmented insertion case has nonempty black middle and uncle
subtrees, arbitrary descendants, and an owned ancestor context. Its native C
proof verifies all three contracts. Whole-claim expansion succeeds and the
expanded source verifies cold. In `click audit`, however, retained verification
of `insert::__rb_insert.contract` exhausts the 750,000-unit simple budget in
`transport`, at C statement 42 / source tactic 129. The whole-claim audit runs
its retained check before its cold comparisons.

This was reproduced on upstream `12df46b57`, whose production code matches the
CLI built at `b508b1db3`. The checked companion model is
`examples/rbtree/rbtree-augmented/rbtree_size_insert_uncle_model.click`.
The complete, not-yet-minimized C sidecar is preserved as
[the reproduction](repros/rbtree-uncle-retained-transport.click.txt). It is kept
outside the example inventory because its expansion audit is blocked.

From the repository root with ordinary C verification configured:

```sh
case_dir=examples/rbtree/rbtree-augmented
case_file="$case_dir/rbtree_size_insert_context_uncle_rotation.click"
cp bugs/repros/rbtree-uncle-retained-transport.click.txt "$case_file"
click verify "$case_file"
click expand --claim 'insert::__rb_insert.contract' \
  --output "$case_dir/.uncle-expanded.click" "$case_file"
click verify "$case_dir/.uncle-expanded.click"
click audit --claim 'insert::__rb_insert.contract' "$case_file"
```

The first three checks pass. The audit fails with:

```text
verification budget exhausted inside tactic `transport` in
`insert::__rb_insert.contract` exhausted its deterministic simple work budget
after 750001 units (750000 limit; statement 42, source tactic 129)
```

`click profile --top 6` on the original and expanded files reports exactly
411,384 units for the explicit statement-42 transport, and 426,341 units for
a nearby fold. Its largest nested costs are explicit-range distinctness,
resource matching, and range coverage. The expensive transport is:

```click
transport(at(before_parent_update, parent->rb_left == node),
          parent->rb_left == node) using {
    at(before_parent_update, parent->rb_left == node);
    parent == p;
    at(before_link_writes, g->rb_left) == parent;
};
```

It follows the checked `__rb_rotate_set_parents` call and a fold of the demoted
node. All its fields are owned or framed by the checked call. The actual
internal cause of the retained/cold discrepancy has not been established.
Do not treat these observations as proof that a particular cache is stale.

Reduce the case while retaining the original two checked helper calls,
field-derived aliases, and the nonempty uncle's recursive ownership. Compare
identical source/expanded checks in a fresh environment and a retained
`C0VerificationSession`; use existing profiling to locate the extra work.

Acceptance requires the audit to pass under the existing proof rules and
limits, with the original Linux C unchanged. Add a regression for retained
verification of the same checked transport and expansion, plus deterministic
multi-size coverage if the fix changes lookup/indexing. Check that branch
scope, withdrawn facts, and snapshot restoration remain respected. Raising
limits or weakening the proof is not a fix.
