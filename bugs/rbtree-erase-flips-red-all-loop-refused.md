# rbtree-erase `flips_red_all` is refused after its loop

Soundness: not soundness. A previously verifying proof is refused; nothing
false is accepted.

`examples/rbtree/rbtree-erase/rbtree_erase_color_flips_red_all.click` verified on
master at 6bd0854ca (2026-10-17). The C source and the sidecar are unchanged
since, so the change is in the verifier.

Two refusals introduced by #1366 are fixed: a loop invariant, and a
`match ... ensuring` fact, calling a typed helper on a reassigned pointer
local could not be lowered at the loop head or at the join (see
`mdtests/a_loop_invariant_supplies_its_typed_call_domains_at_the_head.md` and
`mdtests/a_branch_interface_supplies_its_typed_call_domains_at_the_join.md`).
The sidecar now gets further and is refused in the loop's `preserve` proof.

## Reproduction

```sh
cargo build --release --bin click
target/release/click verify examples/rbtree/rbtree-erase/rbtree_erase_color_flips_red_all.click
```

```text
proof error:
  `rewrite` equality does not occur in the current goal

tactic@1835:91:
  rewrite(iid == sibling);
equality: iid == sibling
goal: tmp1 == sid
```

This first refusal is stale proof text: the verifier already resolves
`iid->rb_left` to `tmp1`, so the rewrite has nothing to rewrite. Replacing that
`have`'s body with `normalize() using { tmp1 == sid; };` passes it, and the
`match ir.model ensuring` join at line 1773 then succeeds. The next refusal is
at line 1854:

```text
proof error:
  `assumption` requires the current goal as an available semantic fact
  current goal is a condition fact

tactic@1854:108:
  assumption();
goal: at(<state A>, tmp1[4]) == at(<state A>, tmp1[4])
```

The source is `have sid->rb_left == at(inner_inputs, sid->rb_left) by
assumption();`. `normalize()` does not prove it either, so the two sides are
not one term although they print identically: the goal display hides what
distinguishes them (probably the memory each read is taken from). Finding that
difference, with `click verify --trace-proof ____rb_erase_color`, is the next
step, and the display that hides it may be its own diagnostic defect.

`rbtree-erase` is a nightly example, so the gate does not run it.

## Intended regression

A reduced gate fixture for whatever rule the line-1854 refusal turns out to
need, and for the goal display if it hides the difference.

## Acceptance criteria

- The command above verifies again, with work close to its earlier 28.8
  million units, after updating the stale rewrite at line 1835.
- A refused goal whose two sides differ never prints them identically.
