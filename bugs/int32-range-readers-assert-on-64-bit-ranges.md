# Readers of 32-bit range bounds stop the verifier on a 64-bit range

A memory range has one of two kinds since #544: signed 32-bit bounds, or
unsigned 64-bit bounds. `CMemoryRange::start()` and `end()`
(`src/kernel/primitives/contracts.rs`) read the bounds as signed 32-bit
indices and assert the kind:

```
a signed 32-bit reader was given a wide memory range
```

The assertion is deliberate: a reader that was never taught the 64-bit
reading must not misread the bounds. But a reader that reaches it stops the
verifier with a panic instead of an answer, and which readers can be
reached with a 64-bit range was established by running the test suite, not
by reading every caller.

Two were found only by converting the Adler-32 trial, on paths no gate test
reaches, and fixed in #552:

- `resources_equal_ignoring_memories` (`src/kernel/assumptions.rs`), reached
  from resource-context equality at a loop back edge;
- the byte renormalization in `memory_range_covers_with_separation`
  (`src/kernel/primitives/resource_algebra.rs`), reached when a coverage
  question has different element widths.

Regression for those two:
`wide_ranges_are_compared_and_refused_without_a_32_bit_reading`
(`src/kernel/tests/resource_tests.rs`). There is no failing case for the
rest, which is the defect: the remaining callers are unaudited.

## Violated invariant

No input a user can write reaches a kernel assertion. A reader that cannot
answer for a 64-bit range answers "unknown" or "not covered", or handles
the kind.

## What to do

Audit every caller of `start()`, `end()` and of the helpers that call them
(`byte_footprint`, `constant_start`, `constant_end`, `signed_constant_start`,
`signed_constant_end`, `start_pointer`, `end_pointer`). For each, either
branch on `wide_bounds()` / `int32_bounds()` first, or show that a 64-bit
range cannot arrive. `bound_terms()` is the accessor for a reader that only
compares or traverses the terms.

## Acceptance criteria

- Each remaining caller is either kind-aware or has a comment saying why a
  64-bit range cannot reach it.
- For every caller made kind-aware, a unit test passes it a 64-bit range.
- A Rust proof with a loop over a `&[u8]` of symbolic length, a nested
  constant window, and calls with mismatched element widths verifies or
  fails with a diagnostic, never a panic.
