# An undefined name in a contract is reported as a tactic failure

## Violated invariant

A contract that names something not in scope is a mistake in the contract,
and its diagnostic should say so at the clause that names it. Today an
undefined name passes declaration checking and surfaces only when a proof
tactic lowers the clause. The report then leads with the tactic:
"checked outcome `simp` did not retain a complete transition for every
pending claim". The actual cause, `unbound variable`, comes last, after a
chain of kernel-lowering detail. Nothing in the report points at the
contract clause.

## Reproduction

`c.c`:

```c
int is_positive(int x) {
    return x > 0;
}
```

`c.click`:

```click
verifying "c.c";

int32 is_positive(int32 x) {
    requires x > 0;
    ensures result == one;
} by {
    execute();
    simp();
}
```

`click verify c.click` reports:

```text
proof error:
  `is_positive.contract` path 0, tactic 1
  checked outcome `simp` did not retain a complete transition for every pending claim
  `ensures result == one` failed for `is_positive.ensures_0` path 0
  could not lower the claim goal
  `is_positive.contract` proof step tactic 1
  could not lower fixed-state obligation
  the kernel lowering produced no path
  every evaluation path ended in a runtime error
  unbound variable `one`

tactic@8:
  simp();
```

Replacing `one` with `1` verifies. An undefined name in `requires` (for
example `requires y > 0;`) also passes declaration checking and is reported
only as `every evaluation path ended in a runtime error` / `unbound variable
`y``, at the function.

The C spellings `true` and `false` hit the same path: `ensures result ==
true;` on a `bool` function reports `unbound variable `true``. The C0
reference documents them as C fallback constants; they are not contract
literals.

## Acceptance criteria

- A contract clause that names an identifier that is neither a parameter,
  `result`, a declared specification function or predicate, nor another name
  the clause's scope binds, is refused during declaration checking, before
  any proof runs.
- The refusal names the identifier and points at the clause, for example
  ``unknown name `one` in `ensures result == one` ``. It names no tactic and
  includes no kernel-lowering chain.
- When the name is `true` or `false`, the message says that these are not
  contract literals and suggests an alternative that works, such as comparing
  with `1`/`0` or another `bool` value.
- Regression mdtests cover an undefined name in `ensures` and in `requires`,
  and `true` in `ensures`, with the expected refusal text.
