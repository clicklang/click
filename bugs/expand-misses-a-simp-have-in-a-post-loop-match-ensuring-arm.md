# `click expand` misses a `simp` `have` in a post-loop `match ... ensuring` arm

Soundness: not soundness. `click verify` accepts the proof; `click expand`
(and so `click-audit`) refuses the site, so two proof tools disagree.

In `mdtests/rb_ascending_walk_to_root.md`, the `match c.model ensuring` after
the loop refutes its `Left` and `Right` arms. Each arm proves `identity ==
parent` with `assumption()`, which the equality closure's constructor
injectivity supplies. Writing the same step with `simp()`:

```click
        Context::Left(identity, grandparent, color, sibling_model, up_model) => {
            unfold(ctx_reroot(Context::Left(identity, grandparent, color, sibling_model, up_model), parent));
            have identity == parent by simp();
            let { sibling: exit_sibling, up: exit_up } = unfold(c);
            contradiction(parent == 0);
        },
```

With both exit arms written with `simp()` (the `Right` arm likewise),
`click verify mdtests/rb_ascending_walk_to_root.md` verifies, but expanding
either `simp` is refused (line numbers from that variant):

```text
$ click expand mdtests/rb_ascending_walk_to_root.md:384:40
click: selected function `rb_root_of` grouped contract proof proof has no source tactic 25
  error kind: proof error
```

The same `have identity == parent by simp();` inside the loop's `preserve`
arms expands. Reproduced on master `8fcee2e9` and with the loop-head and
`branch ensuring` typed-domain changes, so it is not caused by them. The
nightly
`audit::tests::loop_expansion_preserves_match_pointer_theorem_arguments_and_audits_every_site`
audits every site of this mdtest and fails the same way. Earlier fixes of the
same symptom for other positions are
`infeasible_branch_arm_site_audits_instead_of_reporting_a_missing_tactic` and
`smart_have_inside_an_open_scope_audits_instead_of_reporting_a_missing_tactic`
in `src/bin/click-audit/tests.rs`.

## Intended regression

A reduced gate expansion test for a `simp` `have` in an arm of a post-loop
`match ... ensuring` that the arm then refutes.

## Acceptance criteria

- With both exit arms written with `simp()`, both sites expand, re-verify,
  and re-expand to a fixed point, and the nightly audit test above passes.
