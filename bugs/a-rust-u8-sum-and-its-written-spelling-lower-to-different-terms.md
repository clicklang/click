# A Rust `u8` sum and its written spelling lower to different terms

Soundness: no soundness impact. A true claim is refused; nothing false is
accepted. The two terms denote the same value.

A specification that writes the C or Rust operation it is about should
lower to the term the operation produced, so `solve` can close the
restatement. For a Rust `u8` increment it does not. In
`examples/rust-slices/bytes.rs`, `child[0] = value + 1;` lowers through the
compiler's widening, `(((value as u32) + 1) as i32) as u8`, while the
sidecar's `old(bytes[0]) + 1u8` lowers to a different term. The refusal prints
both sides identically:

```text
`solve` failed for `increment_first.contract`
goal: to_integer(old(bytes[0]) + 1) == to_integer(old(bytes[0]) + 1)
```

Spelling the widening does not help: `old(bytes[0]) as u32` lowers to the
`u8` observation itself, so no source text names the `uint32` operand the C
sum adds. The example's `ensures bytes[0] == old(bytes[0]) + 1;` does not
depend on this: `auto` proves it through the lowered sum's Integer identity.
A proof that restates the sum as written still fails.

## Reproduction

From the repository root, replace `increment_first`'s proof in
`examples/rust-slices/bytes.click` with:

```click
} by {
    step_until(function.exit);
    have to_integer(bytes[0]) == to_integer(old(bytes[0]) + 1u8) by solve();
    solve();
}
```

then run `click verify examples/rust-slices`.

## Acceptance criteria

- The written `u8` sum and the lowered Rust sum denote one term (by
  canonicalizing a widening that cannot change the value), or the refusal
  prints the two terms differently and a spelling exists for the operand.
- A regression closes the reproduction's restatement with `solve`.
