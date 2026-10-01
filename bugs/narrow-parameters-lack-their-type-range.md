# Narrow integer parameters lack their type range at entry

## Violated invariant

A value of a narrow C integer type always lies in that type's range: a
`uint8` is in `[0, 255]`, an `int16` in `[-32768, 32767]`. The one standard
fact check should know that at every point where such a value exists. Today a
narrow *parameter* carries no type range at function entry, and returning it
as a wider type does not apply C's integer promotion in a way the facts can
use, so this true contract does not verify:

```c
int32 widen(uint8 x) { return x; }
```

```click
int32 widen(uint8 x) {
    ensures result >= 0;
    ensures result <= 255;
} by { execute(); simp(); }
```

PR #54 made promotion inside expressions file `0 <= x <= 255` as a public path
fact (`add_c_integer_range_execution_pure_facts` in
`src/kernel/eval/expression.rs`), but nothing files the range for a parameter
at entry, and the return conversion does not reach it.

## Intended regression

An mdtest with `uint8`, `uint16`, `int8` and `int16` parameters returned as
`int32`, with `ensures` stating each type's bounds, proved by
`execute(); simp();`. Negatives: claiming a bound one past the range (for
example `result <= 254` for `uint8`) is refused.

## Acceptance criteria

- Every narrow integer value (parameter, local, loaded value, call result)
  carries its type range as a fact the standard check reads, filed once per
  value, not per use.
- The mdtest above verifies; its off-by-one negatives are refused.
- No per-site special case; indexed and constant-size per value.
