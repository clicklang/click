# Expansion prints Click library names the file does not resolve

Soundness: incomplete. A verified proof's expansion fails to parse or is
refused by `click audit`. No false acceptance is involved.

`click expand --claim` and `click audit` print an expanded proof's
references to Click library items in a short form that depends on the
library's module being imported. The written proof itself spells the item in
a form the file can resolve. Two reproductions, both in the corpus:

- `mdtests/memcmp_const_unsigned_char_arguments.md`:
  `click expand --claim compare4.contract` fails with
  ``line 56, column 30: `bytes::equal` names Click library module
  `click::bytes`, which this file does not import``. The file never writes
  `bytes::equal`; the expansion introduces it.
- `mdtests/qualified_library_names.md`: the written
  `apply(click::list::append_left_identity(xs));` in
  `append_nil_by_paths.ensures_0` expands to
  `apply(list::append_left_identity(xs)) using { }`. `click audit` then
  refuses the claim with ``rewritten sidecar changed source outside the
  selected proof unit``.

The audit of `mdtests/` on master after #1048 reports both claims; nothing else
in that audit fails for this reason.

## Acceptance criteria

- An expansion spells each library item so that the file resolves it: as
  written, or fully qualified when its module is not imported.
- `apply(...)` with no premises expands without an empty `using { }`.
- `click audit` passes both claims, and a regression keeps each reproduction.
