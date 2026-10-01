# A refused store through a widened unsigned index doesn't name the element

## Violated invariant

A refusal must name what the user wrote, in source terms. When a store
through a zero-extended `uint32` index is refused for missing ownership, the
message reads:

```
missing resource fact `owns the pointer value at this program point[0..1]`
```

It should name the element, for example `owns values[x]`. The negative
mdtests added in PR #54 (`an_unsigned_index_below_an_unbounded_variable_is_refused.md`,
`an_unsigned_index_below_a_signed_bound_is_refused.md`,
`an_unsigned_index_below_a_wrapped_bound_is_refused.md`) can only pin
`missing resource fact` because of this. Relatedly, `simp`/`arithmetic`
refusals print sign-bit-flipped premises as `internal (no exact Click
spelling) … <bounded opaque operation>`, and a store at index `x - 1u` still
prints the raw `can-store(...)` text.

## Intended regression

Tighten those three mdtests to pin the element name (`values[x]`), and add an
mdtest whose `simp` refusal lists an unsigned premise, pinning that it is
spelled as `x < n` (unsigned) rather than as an internal term.

## Acceptance criteria

- Missing-resource refusals for stores and loads through any index type name
  the source element.
- Unsigned premises and goals are spelled as unsigned comparisons in every
  refusal and proof context.
- No message contains `the pointer value at this program point` or
  `no exact Click spelling` for these shapes.
