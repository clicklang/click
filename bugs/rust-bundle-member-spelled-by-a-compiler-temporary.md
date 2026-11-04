# Rust loop bundle member is spelled by a compiler temporary

Soundness: diagnostic-only. The refused member is still refused; only its
printed spelling is wrong, so no false claim verifies.

A refused back-edge bundle member of a Rust loop names the value
`steps + 1` by the compiler temporary that holds it, `__rust_mir_6`, which
no proof can write. Every printed fact must be spellable
(`docs/internals/spellability.md`); the value's spelling is
`at(<iteration entry>, steps) + 1`, as the same member of a C loop prints.

## Reproduction

`bindings.rs`, locked as a Rust unit with root `program_bindings::count`
(the layout of `design/charon-trial/program-bindings`):

```rust
pub fn count(n: u32) -> u32 {
    let mut steps = 0;
    while steps < n {
        steps += 1;
    }
    steps
}
```

```click
verifying "bindings.rs";

fn program_bindings::count(n: u32) -> u32 {
    requires n <= 1000u32;
    ensures result == n;
} by {
    step_until(loop(0));
    loop {
        decreases n - steps;
        invariant steps <= n;
        invariant steps == 2 * iterations;
    }
}
```

`click verify` refuses the second invariant, as it should, but prints

```
`(let integer_value: Integer = to_integer((__rust_mir_6 as u32)); integer_value) == (2 * (iterations + 1))` remained open
```

## Acceptance

- The refused member prints the value without a compiler temporary, for
  example `to_integer(at(<iteration entry>, steps) + 1u32) == 2 * (iterations + 1)`,
  and that spelling lowers back to the member.
- A regression in `tests/rust_import.rs` checks the printed member of this
  reproduction contains no `__rust_mir_`.
