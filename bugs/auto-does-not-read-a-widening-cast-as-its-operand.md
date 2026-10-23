# `auto` does not read a widening cast as its operand

Soundness: incomplete. A provable goal is refused; nothing false verifies.

## Violated invariant

A widening cast keeps its value (`design/machine-integers.md`, conversion
table: widening needs no premise). `auto` does not use that identity:

```click
theorem widened_observation(a: uint32) {
    ensures to_integer((int64)a) == to_integer(a) by auto();
}
```

`auto` refuses: "could not establish `to_integer(((int64)a)) ==
to_integer(a)`". So a goal such as `to_integer((int64)a + (int64)b) <=
to_integer(4294967295i64)` from the Integer bound of `a + b` also fails.

Proofs cite `click::integer::uint32_widened_add_guard_by_integer_bound`
for the widened case instead: about 55 sites in
`design/adler32/project/adler2`.

## Reproduction

Save the theorem above as `cast.click` and run `click verify cast.click`.

## Acceptance

- `auto` proves the observation of a widening cast equal to its operand's,
  at every widening pair, and the widened guard above from the Integer
  bound.
- The `uint32_widened_add_guard_by_integer_bound` citations it replaces are
  removed.
