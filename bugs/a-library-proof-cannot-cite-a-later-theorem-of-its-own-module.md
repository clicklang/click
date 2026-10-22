# A library proof cannot cite a later theorem of its own module

Soundness: incomplete. A valid library proof is refused; nothing false verifies.

## Violated invariant

A module's theorems are in scope in every proof in that module. The standard
library's own entry point (`crate::surface::verify_standard_library`) refuses
the body of `click::integer::uint32_add_guard_by_integer_bound`:

```text
standard library failed: `click::integer::uint32_add_guard_by_integer_bound.ensures_0`
tactic 1: `apply` failed: unknown theorem `click::integer::uint32_subtract_to_integer`;
it is declared in Click library module `click::integer`, so add `import click::integer;`
```

The proof is in `library/integer.click` itself, so the suggested import is
wrong: the cited theorem is a sibling declared further down the same file
(`uint32_add_guard_by_integer_bound` is the second theorem of the module,
`uint32_subtract_to_integer` the fourth), so declaration order is the
suspected cause; it has not been confirmed by reordering. Sidecars that apply
the theorem are unaffected, since they take library theorems as declarations.

## Reproduction

```console
cargo test --lib standard_library_theorems_are_proved_by_their_own_entry_point -- --ignored
```

This nightly test failed on `library/integer.click` as of commit `0c3389ed`
with the message above. `uint32_add_guard_by_integer_bound` has since been
removed (a built-in check now accepts the Integer reading of its condition),
so the test passes again; the library no longer has a proof citing a later
sibling. To reproduce, add a proved theorem to `library/integer.click` whose
body applies a theorem declared after it, and rerun the test.

## Acceptance

- `standard_library_theorems_are_proved_by_their_own_entry_point` passes with
  the library unchanged.
- A library proof may cite any theorem of its own module regardless of
  declaration order, or the reference states the order rule and the diagnostic
  names it instead of suggesting an import.
