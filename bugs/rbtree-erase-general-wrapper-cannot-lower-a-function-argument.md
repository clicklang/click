# The rbtree erase wrapper cannot lower a function passed as an argument

Soundness: no soundness impact. A valid proof is refused; nothing false is
accepted.

`issues/rbtree-example.md` records that
`examples/rbtree/rbtree-erase/rbtree_erase_general_wrapper.click` verifies
`rb_erase` on top of the general unlink contract. On current master it is
refused at the call that passes the C function `dummy_rotate` as an
argument:

```text
proof error:
  could not lower call argument
  the kernel lowering produced no path
  every evaluation path ended in a runtime error
  unbound variable `dummy_rotate`

tactic@90:
  let { whole: whole } = step(____rb_erase_color(rebalance, root, dummy_rotate), { c: deficit });
```

The C source is the unchanged Linux pattern (`rb_erase.c`):

```c
static inline void dummy_rotate(struct rb_node *old, struct rb_node *new) {}
...
		____rb_erase_color(rebalance, root, dummy_rotate);
```

The invariant is that a call step whose argument names a function in the
verified translation unit lowers that argument to the function's address, as
the C call does. The example is in the nightly-only list in
`tests/examples.rs`, so the ten-minute gate does not run it.

## Reproduction

From the repository root, with no changes:

```sh
click verify examples/rbtree/rbtree-erase/rbtree_erase_general_wrapper.click
```

## Acceptance criteria

- The wrapper verifies again, with the call written as above.
- A gate regression reduces the pattern: a sidecar steps a call that passes a
  translation-unit function as a function-pointer argument, through a named
  call step with a resource binding.
