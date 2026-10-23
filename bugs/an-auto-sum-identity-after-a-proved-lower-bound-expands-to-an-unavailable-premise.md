# An `auto` sum identity after a proved lower bound expands to an unavailable premise

Soundness: incomplete. `auto` accepts the proof and its expansion is refused;
nothing false verifies, but expansion and audit fail on an accepted proof.

## Violated invariant

A proof that verifies with `auto()` must expand to a simple certificate that
reverifies (`click expand`, `click audit`). In a C function proof, `auto()`
proves the in-range native sum identity `to_integer(q + 1i64) ==
to_integer(q) + 1`, but once the context holds a proved Integer lower bound
`-9223372036854775808 <= to_integer(q)`, the expanded certificate for the
sum's lower range check cites a premise the checker reports as not exactly
available.

## Reproduction

`inc.c`:

```c
#include <stdint.h>
int64_t inc(int64_t q) { return q; }
```

`inc.click`:

```click
verifying "inc.c";

int64 inc(int64 q) {
    requires to_integer(q) <= 9223372036854775806;
    ensures true;
} by {
    have -9223372036854775808 <= to_integer(q) by auto();
    have defined(q + 1i64) by simp();
    have to_integer(q + 1i64) == to_integer(q) + 1 by auto();
    execute();
    simp();
}
```

`click verify inc.click` succeeds. `click expand --output x.click inc.click:9`
fails: "expanded proof did not verify: `inc.contract` tactic 2: `have` failed
for `to_integer((q + 1i64)) == (to_integer(q) + 1)`: ... have body tactic 1 >
have body tactic 1: integer certificate premise 0 is not exactly available"
(goal `-9223372036854775808 <= to_integer(q) + 1`).

Deleting the first `have` line makes the expansion reverify. The same proof as
a pure `theorem` over `q: int64` also expands correctly. The `if 0 < q { ... }`
variant of this pattern is how the fee-rounding fixtures hit it:
`tests/fixtures/cpp-verification/fee-rounding/Rounded.click` and the
Bitcoin `FeeFracDivBounded.click` / `FeeFracDivResultFitUp.click` sidecars
(correction `quot + 1i64` inside `if 0 < mod`), whose full-expansion tests
fail when the site's `apply(int64_add_to_integer(quot, 1i64));` is replaced by
`have to_integer(quot + 1i64) == to_integer(quot) + 1 by auto();`. Those sites
still cite the bridge lemma for this reason.

## Acceptance criteria

- The reproduction's expansion reverifies, as a regression beside the
  existing `auto` expansion coverage.
- The three fixture sites above can state the identity `by auto();` and their
  full-expansion tests pass; then remove their `int64_add_to_integer` citation.
