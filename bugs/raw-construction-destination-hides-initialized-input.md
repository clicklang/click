# Raw construction destinations hide initialized constructor inputs

At `67d36e1aed2fcc80b8cc56d905dba53a71772942` (PR 646), existing C++ RAII
constructor proofs fail with `read of uninitialized storage`. This reproduces
locally with freshly compiled tests and in the PR's unit, mdtest and example
CI shards. The 5,357 passing library tests do not cover this integration failure.

## Reproduction

With the pinned C++ exporter configured, run:

```console
cargo nextest run --test cpp_import -E 'test(explicit_constructor_local_verifies_as_a_modular_call) | test(scalar_int32_profile_unwinds_one_guard_on_both_paths)' --no-fail-fast
MDTEST_FILTER=cpp_one_guard_unwind cargo nextest run --test mdtests
CLICK_EXAMPLE=basic-cpp cargo nextest run --test examples -E 'test(example_projects)'
```

The first command was reproduced locally. CI also reproduces the existing
`cpp_one_guard_unwind.md`, `cpp_two_guard_unwind.md`,
`cpp_guard_unwind_before_second.md`, and `examples/basic-cpp/with_restore.click`
failures. Preserve those original source patterns and contracts.

The constructor has authority for its own value fields and the input slot. It
reads the input to save the original value, then writes the slot. The constructor
body now fails before it can establish its existing postconditions. Its reported
context includes ownership composition for the destination and the input slot.

## Invariant and investigation

A raw output footprint must remain unwritten, while other contract-justified
initialized inputs remain readable. Permission must not initialize the output,
and distinct symbolic pointer names must not imply separation.

Proof-entry naming now receives the checked entry fact context and the execution
overlap query accepts explicit byte-separation facts. That repaired the separate
returned-observer regression, but this example supplies separation only through
ownership of value fields. Those fields do not cover padding.

The constructor binder now checks structural destination selection against a
complete declaration, explicit embedded-record boundary, or retained native
construction input requirement. Raw footprints alone no longer satisfy that
selection. This check still does not establish nominal C++ identity or the
scalar input's designation. Contract certification uses the same binder and
does not add the missing scalar evidence. A field-separation shortcut would
therefore still lack justification at callers and symbolic body entry.

The [implementation sequence](../design/cpp-object-model.md#constructor-padding-implementation-sequence)
starts with persistent declaration metadata, then retained subobject boundaries
and checked pointer designation at calls. Installing a destination-sized block
at symbolic entry would incorrectly assume the constructor targets a complete
allocation; that entry must continue to support an object inside a larger parent.

## Acceptance

- Restore the unchanged constructor, cleanup mdtests and basic C++ example in
  ordinary, expanded and retained verification where those fixtures exercise it.
- Preserve refusal of no-op constructors, missing field writes, output reads
  before writes, aliased raw reads without adequate evidence, and no-op ordinary
  initialized-range guarantees.
- Use checked entry/resource evidence consistently, with indexed relevant-range
  work. Do not invent destination freshness, seed output values, weaken the
  contracts, quarantine tests, or raise budgets.

The [object-model design](../design/cpp-object-model.md#contracts-proof-entry-and-modular-calls)
records the shared invariant and makes restoration a stabilization prerequisite.
