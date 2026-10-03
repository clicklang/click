# Rust symbolic multiplication does not match its explicit safety precondition

Checked execution should discharge an unsigned multiplication panic obligation
when that exact safety condition is present in the contract.

In a temporary copy of
`design/charon-trial/assignment-operators/operators.click`, replace the
`U32X4_mul_assign_u32` requirement `rhs == 2u32` with `rhs <= 4u32`. For each
lane `i` from 0 through 3 add:

```c
requires rhs == 0u32 or self->_0[i] <= 4294967295u32 / rhs;
```

Leave the source and all other contracts unchanged. With the same locked
artifact, `click verify` refuses the first `execute()` at the `Rust mul panic
check`. The displayed obligation is
`((uint32)__rust_checked_2 == 0u32) || ((uint32)__rust_checked_1 <= (-1u32 / (uint32)__rust_checked_2))`.
Both the lane bound and explicit safety premise are present. Spelling the maximum
as `-1u32` instead of `4294967295u32` still fails. Requiring `rhs == 2u32` verifies.

Investigate unsigned constant normalization, captured operands and checked
matching of disjunctions. This is a proof completeness report, not evidence that
an overflowing multiplication is accepted.

Acceptance: a primitive unsigned multiplication and the unchanged source method
verify under the explicit general safety premise; expanded proofs recheck and
missing bounds, zero-divisor arithmetic and overflowing inputs remain rejected.
