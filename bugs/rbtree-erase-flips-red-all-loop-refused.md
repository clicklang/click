# rbtree-erase `flips_red_all` is refused after its loop

Soundness: not soundness. A previously verifying proof is refused; nothing
false is accepted.

`examples/rbtree/rbtree-erase/rbtree_erase_color_flips_red_all.click` verified on
master at 6bd0854ca (2026-10-17). The C source and the sidecar are unchanged
since, so the change is in the verifier.

It was first refused at its loop (`loop has neither a safe exit nor a safe
iteration`). That came from #1366: a loop invariant calling a typed helper on
a reassigned pointer local could not be lowered at the loop head. The loop
head now assumes those call domains (see
`mdtests/a_loop_invariant_supplies_its_typed_call_domains_at_the_head.md`),
and the sidecar gets further but is refused in the loop's `preserve` proof.

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

This first refusal is stale proof text, not a defect: the verifier already
resolves `iid->rb_left` to `tmp1`, so the rewrite has nothing to rewrite.
Replacing that `have`'s body with `normalize() using { tmp1 == sid; };`
passes it and reaches the next refusal, at line 1836:

```text
`____rb_erase_color.contract` tactic 10 (`loop`), `preserve` tactic 106
could not abstract `branch ensuring` fact
the kernel lowering produced 0 paths, not one
```

Suspected, not confirmed: the same #1366 rule at a different interface.
`branch ensuring` facts are checked in each arm and assumed after the join
(`src/surface/proof/cursor_execution.rs`), but the join lowers them with
ordinary lowering, which refuses a typed helper call whose pointer argument
has no object-class evidence at the joined state.

`rbtree-erase` is a nightly example, so the gate does not run it.

## Intended regression

A reduced gate fixture with a `branch ... ensuring` fact that calls a typed
helper on a pointer the arms reassign, beside a negative where an arm cannot
establish the pointer's class.

## Acceptance criteria

- The command above verifies again, with work close to its earlier 28.8
  million units, after updating the stale rewrite at line 1835.
- A gate regression covers the `branch ensuring` lowering rule, if that is
  the cause.
