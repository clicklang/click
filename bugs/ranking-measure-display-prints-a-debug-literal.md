# A ranking measure's display prints a literal as Rust Debug output

Soundness: diagnostic-only. The measure is checked as written; only its
printed spelling is wrong.

A loop's `decreases n - t + 1u32` is printed in the bundle note as
`to_integer(n) - to_integer(t) + to_integer(Value(UInt32(UInt32Constant(1))))`:
the `1u32` literal is rendered with its Rust `Debug` form, which no proof can
write. The kernel's measure display (`termination::c_ranking_measure_display`)
falls back to `Debug` for a literal value.

## Reproduction

A Rust unit with root `bool_flag::settle`:

```rust
pub fn settle(n: u32) -> u32 {
    let mut done = false;
    let mut t = 0u32;
    while !done {
        if t < n {
            t += 1;
        } else {
            done = true;
        }
    }
    t
}
```

```click
verifying "flag.rs";

fn bool_flag::settle(n: u32) -> u32 {
    ensures result == n;
} by {
    step_until(loop(0));
    loop {
        decreases n - t + 1u32;
        invariant t <= n;
    }
}
```

`click verify` refuses the measure (it does not decrease on the pass that
sets `done`), and its note prints
`to_integer(n) - to_integer(t) + to_integer(Value(UInt32(UInt32Constant(1))))`.

## Acceptance

- The note prints the literal as written, `1u32`, or as its Integer value.
- A regression checks the printed note contains no `Value(`.
