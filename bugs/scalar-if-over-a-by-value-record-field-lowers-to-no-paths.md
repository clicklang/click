# A scalar `if` over a by-value record parameter's field lowers to no paths

Soundness: incomplete. A true postcondition is refused before any proof
search; no false claim is accepted.

A postcondition whose value is a scalar `if` reading a field of a by-value
record parameter cannot be lowered: the claim fails with "the kernel lowering
produced 0 paths, not one". The same claim split into two implications
verifies, and a scalar `if` over scalar parameters verifies
(`tests/fixtures/rust-verification/references.click`, `choose`), so the
lowering of an `if` whose condition or branch is an aggregate parameter field
read is what fails.

Reproduction (measured on master `a3f63e699`, the merge of #1599), a crate
unit `pairs` with root `pairs::pick`:

```rust
pub struct Pair {
    flag: u8,
    value: u32,
}

pub fn pick(p: Pair) -> u32 {
    if p.flag != 0 { p.value } else { 0 }
}
```

```click
verifying "pair.rs";

fn pairs::pick(p: pairs::Pair) -> u32 {
    ensures result == (if p.flag != 0u8 { p.value } else { 0u32 });
} by {
    execute();
    simp();
}
```

`click verify` reports, for `pairs::pick.ensures_0`: "could not lower the
claim goal ... could not lower fixed-state obligation ... the kernel lowering
produced 0 paths, not one". Replacing the clause with
`ensures p.flag != 0u8 implies result == p.value;` and
`ensures p.flag == 0u8 implies result == 0u32;` verifies.

Acceptance criteria:

- The reproduction verifies, and `ensures result == (if p.flag != 0u8 {
  p.value } else { 1u32 });` is refused at the claim, not at lowering.
- A regression covers a scalar `if` over a by-value record parameter's field
  in a postcondition, with the field in the condition and in a branch.
