# rbtree-erase `flips_red_all` loop is refused on master

Soundness: not soundness. A previously verifying proof is refused; nothing
false is accepted.

`examples/rbtree/rbtree-erase/rbtree_erase_color_flips_red_all.click` verified on
master at 6bd0854ca (2026-10-17). It is refused at 8ac4c0311. The C source
and the sidecar are the same in both, so the change is in the verifier.

## Reproduction

```sh
cargo build --release --bin click
target/release/click verify examples/rbtree/rbtree-erase/rbtree_erase_color_flips_red_all.click
```

```text
proof error:
  execution proof traversal at statement(5) is missing prerequisite (loop has neither a safe exit nor a safe iteration)
  false == true
  C statement at rb_erase_color.c:11:2
  `while (true) { …`

tactic@1268:
  loop {
      owns c: ctx_at(node, root);
      ...
```

At 6bd0854ca the same command verifies, spending about 28.8 million tactic
work units. `rbtree-erase` is a nightly example, so the gate does not run
it. `bugs/nightly-pointer-theorem-loop-audit-rejects-original.md` reports the
same message for a different fixture and may share the cause.

## Intended regression

The nightly examples run covers this file. Bisect the change between
6bd0854ca and 8ac4c0311, and add a reduced gate fixture for the loop rule it
broke.

## Acceptance criteria

- The command above verifies again, with work close to its earlier 28.8
  million units.
- The commit that broke it is named, and a gate regression covers the rule
  it changed.
