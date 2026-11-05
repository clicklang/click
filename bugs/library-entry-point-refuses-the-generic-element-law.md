# The library entry point refuses the generic element separation law

Soundness: incomplete. A kernel law used successfully at its instances is
refused at its own entry point; nothing false is accepted.

`separation::elements` became `elements<T, I>(p: T*, i: I, j: I)` in
1399cb981, so one law covers `int32`, `int64`, and `uint64` indices. The
standard-library entry point (`verify_standard_library`) checks a generic
theorem once at rigid types. A non-pointer type parameter becomes a rigid
algebraic type, which cannot index `p[i]`, so the check stops with "cannot
substitute non-C-fragment expression for `i` inside C fragment `i`". The
nightly test `standard_library_theorems_are_proved_by_their_own_entry_point`
has failed this way since.

## Reproduction

`cargo nextest run --lib --run-ignored all standard_library_theorems_are_proved_by_their_own_entry_point`
panics with the message above. Applying the law at an `int32` index
(`mdtests/separation_elements_signed.md`) verifies.

## Acceptance

- The entry point checks `separation::elements` at each index type its
  kernel builder admits (`int32`, `int64`, `uint64`), and a forged
  declaration (no disequality premise, or `p[i]` twice) is refused.
- A gate unit test covers this without running the whole library.
