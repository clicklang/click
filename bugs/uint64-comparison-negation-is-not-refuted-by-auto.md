# A `uint64` comparison is not refuted by its branch's negation

Soundness: incomplete. `auto` and `simp` fail to close true goals; no false
acceptance is known.

The `contradiction` reference (`docs/reference/tactics/index.md`) states that
a comparison and its arithmetic negation, such as `x < 0` beside `x >= 0`,
count as opposite polarities. On `int32` this holds for `auto`: a branch on
`x >= 32` closes `x < 32 implies result == x` on the other path. On `uint64`
the same contract fails in both directions: the path where `x >= 32u64` does
not refute the hypothesis `x < 32u64`, and the path where `x < 32u64` does
not refute `32u64 <= x`. Spelling the hypothesis in the branch's own
polarity, `not (x >= 32u64)`, verifies, so the missing step is the
recognition of the arithmetic negation for unsigned 64-bit comparisons.

Found while giving `label_fit` (`examples/label-build-flags/label.click`) an
exact contract; its proof now splits with `if` and closes the opposite arm
with `uint64_less_equal_less_than_transitive` and `contradiction`.

## Reproduction

```c filename=fit.c
uint64 fit(uint64 x)
{
	if (x >= 32)
		return 31;
	return x;
}

int32 fit32(int32 x)
{
	if (x >= 32)
		return 31;
	return x;
}
```

```click
verifying "fit.c";

uint64 fit(uint64 x) {
    ensures x < 32u64 implies result == x;
    ensures 32u64 <= x implies result == 31u64;
} by auto;

int32 fit32(int32 x) {
    ensures x < 32 implies result == x;
    ensures 32 <= x implies result == 31;
} by auto;
```

`fit32` verifies; `fit` fails with `case: [x >= 32u64]` beside the unclosed
goal `x < 32u64 implies result == x`.

## Acceptance

- The reproduction verifies as an mdtest (`expect pass`).
- `label_fit`'s proof in `examples/label-build-flags/label.click` and in
  `docs/concepts/own-project.md` returns to `execute()` per arm, or to
  `by auto`.
