# Signed arithmetic in a spec `match` arm does not lower

Soundness: incomplete. A valid claim is refused at lowering; nothing false
verifies.

A contract's spec-level `match` on an enum may compute in its arms. An arm
with machine signed arithmetic, `0i32 - x` or `-1i64 * x`, makes the claim
unloweable: `simp` reports `could not lower the claim goal ... the kernel
lowering stopped at no single evaluation path`, even with the arm's operand
bounded by a `requires`. The same arms without arithmetic (`x`, `x as i32`,
`0i32`) lower and verify. Unsigned arithmetic in an arm was not checked.

## Reproduction

`e.rs`, a Rust unit:

```rust
pub enum Amount {
    Credit(u32),
    Debit(i32),
}

pub fn value(amount: Amount) -> i32 {
    match amount {
        Amount::Credit(x) => x as i32,
        Amount::Debit(x) => -1 * x,
    }
}
```

```click
verifying "e.rs";
fn value(amount: Amount) -> i32 {
    requires match amount { Amount::Credit(x) => 0i32, Amount::Debit(x) => x } >= -1000000i32;
    requires match amount { Amount::Credit(x) => 0i32, Amount::Debit(x) => x } <= 1000000i32;
    ensures result == match amount {
        Amount::Credit(x) => x as i32,
        Amount::Debit(x) => 0i32 - x,
    };
} by { execute(); simp(); }
```

```text
`ensures result == match amount { Amount::Credit(x) => (x as i32), Amount::Debit(x) => (0 - x) }` failed for `value.ensures_0` path 0
could not lower the claim goal
could not lower fixed-state obligation
the kernel lowering stopped at no single evaluation path
```

An explicit proof `match amount { Amount::Credit(x) => { execute(); simp(); },
Amount::Debit(x) => { execute(); simp(); } }` fails the same way in the
`Credit` arm, where the `Debit` arm's arithmetic is not even taken.

## Acceptance criteria

- The reproduction verifies as written.
- A claim with a wrong arm, `Amount::Debit(x) => 1i32 - x`, is refused as an
  unproved goal, not at lowering.
- The regression is beside the enum fixtures,
  `tests/fixtures/rust-verification/enums.click`.
