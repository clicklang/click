# An explicit proof of a function's early returns hits proof nesting bounds

## Violated invariant

Existing C is the verification boundary: a function inside the supported
semantics must be provable without reshaping it. A proof written with simple
tactics only must also be writable for it, since that is the form the
simple-verification contract governs and the form `click expand` produces.

A function with a run of early returns,

```c
if (a == 0) { return 0; }
if (a == 1) { return 1; }
...
return -1;
```

is proved explicitly by one proof `if` per return, each nested in the `else`
arm of the one before it, because every later statement runs only on that
arm. So the proof's nesting grows with the number of returns, and two
independent bounds stop it:

- From 23 returns the checked proof drivers refuse the proof:

  ```text
  proof error:
    `g.contract`
    this proof nests 24 execution regions; the checked proof drivers support at most 11. Move an inner `match`, `branch`, or proof `if` into a contracted helper, or prove part of it in a `have`.
  ```

  The message is also wrong about the bound it names. The same proof with 22
  returns nests 23 regions and verifies, so the drivers do not stop at 11
  (`MAX_CHECKED_PROOF_REGION_NESTING` in
  `src/surface/proof/checked_drivers/proof_execution.rs`). The comment above
  that constant says a continuing arm's descent "is charged at the
  continuing arm's level, so it can exceed the written nesting"; the
  diagnostic reports the written count against a limit the proof was not
  actually held to.
- From 28 returns the parser refuses it first:

  ```text
  syntax error:
    proof nesting exceeds Click's supported depth of 32
  ```

The grouped `execute(); simp();` proof of the same function verifies at 64
returns, so the function is provable; what cannot be written is its
expansion. `click expand` of that proof's `execute()` at 24 returns fails:

```text
click: expanded proof did not verify: `g.contract`: this proof nests 25 execution regions; the checked proof drivers support at most 11. ...
```

Measured on 2026-10-06 with `early_return_fan_out` and
`early_return_fan_out_explicit_proof` from
`src/surface/tests/scaling_tests.rs`: the explicit proof verifies at every
size from 8 to 22 returns, is refused by the drivers at 23 to 27, and by the
parser from 28.

## Intended regression

A test over `early_return_fan_out_explicit_proof` at 16, 32, and 64 returns
that verifies each explicit proof, and a second that expands the grouped
`execute(); simp();` proof of `early_return_fan_out` at those sizes and
re-verifies the expansion. Keep a negative case whose postcondition is false
on the last path. `explicit_early_return_proof_is_near_linear_in_its_returns`
should then run to 64 returns.

## Acceptance criteria

- The explicit proof of a function with `P` sequential early returns
  verifies for `P` well past 22, either because a terminal arm no longer
  costs a level of nesting in the continuing arm or because the proof has a
  flat spelling for sequential returns.
- `click expand` of the grouped proof of such a function produces source
  that verifies at the same sizes.
- When a nesting bound does refuse a proof, the diagnostic names the bound
  that was actually reached.
- `scripts/check.sh` passes.
