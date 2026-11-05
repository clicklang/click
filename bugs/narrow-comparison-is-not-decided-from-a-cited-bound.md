# A narrow comparison is not decided from a cited bound

Soundness: incomplete. A true `uint8` comparison that the listed premise
states exactly is refused; nothing false is accepted.

Since the native narrow comparisons (#2240), `normalize() using` and
`solve() using` decide a comparison with a constant from a cited bound on the
same operand only at 32 and 64 bits. An 8- or 16-bit comparison keeps its own
constant's format, and `constant_comparison_subject` in
`src/kernel/proof/fact_reasoning.rs` recognizes only 32- and 64-bit
constants, so the route is never tried. The library proof of
`format::padded_digit_lower_bound` (unchanged since it passed at 29319906c)
fails the standard-library entry point in its else arm.

## Reproduction

```click
theorem else_arm(b: uint8, x: uint64, y: uint64) {
    requires 48u8 <= b;
    requires not (x < y);
    ensures 48u8 <= (if x < y { 48u8 } else { b }) by {
        solve() using { not (x < y); 48u8 <= b; };
    }
}
```

Refused with "`solve() using` could not prove the current goal from only its
listed premises". The same theorem at `uint32` or `uint64` verifies, and so
does `normalize() using { not (x < y); 48u32 <= b; }`. The trace shows the
reduced goal `uint8 <=(48u8, b)` is exactly the cited condition.

## Acceptance

- The reproduction verifies, as do a strict and a weakened (`50u8 <= b`
  gives `48u8 <= b`) form; `40u8 <= b` still does not give `48u8 <= b`.
- `format::padded_digit_lower_bound` passes the library entry point
  (`standard_library_theorems_are_proved_by_their_own_entry_point`).
