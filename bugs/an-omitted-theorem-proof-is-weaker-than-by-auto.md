# An omitted theorem proof is weaker than `by auto()`

Soundness: incomplete. A provable claim is refused; nothing false verifies.

## Violated invariant

Omitting a proof clause uses the default prover, `auto`
(`docs/reference/language/index.md`, "Postconditions"), and `by auto();` is
the same as omitting the proof clause (`docs/reference/tactics/index.md`,
"Automation and search"). On a pure theorem's `ensures` the two differ: an
omitted proof runs `simp` alone, while `by auto();` runs the solver around
`simp` and closes goals `simp` misses.

```click
theorem omitted(left: int32, right: int32) {
    requires defined(left + right);
    ensures to_integer(left + right) == to_integer(left) + to_integer(right);
}

theorem omitted_order(a: int32, b: int32, c: int32) {
    requires a < b;
    requires b < c;
    ensures to_integer(a) + 2 <= to_integer(c);
}
```

Each is refused: "`simp` failed for `omitted.ensures_0`: could not establish
`to_integer((left + right)) == (to_integer(left) + to_integer(right))`", and
the same for `omitted_order`. Adding `by auto();` to either `ensures` makes it
verify.

## Reproduction

Save the theorems above as `omitted.click` and run `click verify
omitted.click`. Then append ` by auto()` before each `ensures` semicolon and
rerun: both verify.

## Acceptance criteria

- An omitted `ensures` proof on a pure theorem closes every goal that
  `by auto();` closes, or the reference states the difference and the
  diagnostic names it.
- A regression mdtest covers both theorems above with the proof omitted.
