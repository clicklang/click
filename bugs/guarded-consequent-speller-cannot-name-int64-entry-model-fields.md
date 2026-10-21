# The guarded-consequent speller cannot name int64 model fields at entry

Soundness: incomplete. A true postcondition is refused; nothing false verifies.
The refusal comes from `simp` failing to spell a guarded fact it holds, not
from a weaker kernel judgment.

## Violated invariant

A callee postcondition over `int64` arithmetic, stated by exact observations
(`to_integer(st.total) == to_integer(old(st.total) + result)`), is recorded as
a guarded fact: "`old + got` does not overflow implies `total == old + got`".
`simp`'s guarded-consequent closure
(`src/surface/proof/guarded_consequents.rs`) proves the guard and extracts the
equation. It does so for `int32`. For `int64` it offers nothing, because
`GuardedTermSpeller::term` returns `None` for the two leaf variables: the
model field's value at entry (`old(st.total)`) and the loaded local `got`.
The guard and the consequent both fail to spell, so the candidate is dropped.

## Reproduction

`mdtests/guarded_postcondition_int64_bounds.md` with its two postconditions
in the exact spelling:

```
    ensures to_integer(st.total) == to_integer(old(st.total) + result);
    ...
    ensures result == 1 implies to_integer(st.total) == to_integer(old(st.total) + 1);
```

`click verify` refuses `caller`: `simp` leaves
`got == 1i64 implies st.total == old + 1i64` open. The `int32` twin,
`mdtests/int32_defined_from_bounds.md` (`bump`/`caller`), verifies with the
same spelling, and `click expand` shows its closure
(`intro(); have defined(...); extract(...); rewrite(...)`).

## Acceptance

- The reproduction verifies, and its `caller` expansion contains the
  `int64_defined` certificate for `defined((old(st.total) + ...))`.
- `int64_guarded_postcondition_expands_to_int64_defined_and_reverifies`
  (`src/surface/tests/expansion_tests.rs`) passes against the exact spelling.
