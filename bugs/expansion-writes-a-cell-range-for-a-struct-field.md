# Expansion writes a cell range inside a struct, which reads back as a count of structs

## Violated invariant

`click expand` emits Click that verifies. A fact it writes must mean, when
parsed, what the checked proof used.

## Reproduction

```sh
click expand --claim probe_contract.contract \
    mdtests/loop_invariant_through_loaded_pointer_field.md
```

fails with

```
expanded proof did not verify: ... `instantiate using` premise 21
`at(function.entry, viewable(j[2..3]))` is not an available exact fact
```

`j` is a `struct job *` with `{ int32 *p; int32 lo; int32 hi; int32 v; }`.
The fact the proof used is that the field `lo` is loadable: bytes 8 to 12 of
the struct. The expansion spells that as four-byte cells counted from `j`.

## Cause

Since #390 a range on a struct pointer counts structs, so `j[2..3]` parses as
the third whole `struct job`, not as cell 2. The synthesis of a loadable
fact's surface form still builds a cell range over a named base:
`synthesize_named_range_loadable_segment` and its neighbours in
`src/surface/proof/surface_synthesis.rs` construct a
`ContractSegmentSurface::Range` with the base's element width, which is 4
for a struct pointer.

The surface has one spelling for those bytes now, the field: `viewable(j->lo)`.
The synthesis has to build the field segment the parser builds for that
spelling (`field_segment_from_metadata` in `src/surface/parser.rs`), for a
range that is exactly one field, and decline otherwise. A field's slot runs
to the next field, so a loadable range that stops before trailing padding is
not the field's slot and needs care.

The diagnostic printers were given the place rule in #393
(`describe_struct_place_range`); `describe_source_range` gets it with this
bug's filing, but the fact above does not go through a printer.

## Effect on the audit

`mdtests/loop_invariant_through_loaded_pointer_field.md` is excluded from the
nightly audit in `scripts/check.sh`. Remove the exclusion with this bug.

## Intended regression

The reproduction as a whole-claim expansion test in
`src/surface/tests/expansion_tests.rs`, and a second fixture whose loadable
fact is a field followed by padding.

## Acceptance

- The reproduction expands and the result verifies.
- No expansion writes `p[a..b]` for a struct pointer `p` unless it means
  `b - a` structs.
- `scripts/check.sh --audit` passes without the exclusion.
