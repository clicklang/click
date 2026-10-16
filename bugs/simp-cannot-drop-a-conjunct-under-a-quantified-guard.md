# `simp` cannot drop a conjunct under a quantified postcondition's guard

Soundness: incomplete. A true claim is refused; nothing false is accepted,
because the refusal comes from the smart search finding no derivation.

## Violated invariant

A guarded universal fact `forall k { G implies A and B }` entails
`forall k { G implies B }`. `memset`'s library contract states
`(0u64..bytes).all(|k| { defined(destination[k]) and destination[k] == value })`.
A caller that states only the values, the form `bytes::all_equal` unfolds to,
is refused by `execute(); simp();`. The trace shows no memory query: the
postcondition never reaches the check as a premise. The same claim written
with the `defined(..)` conjunct verifies.

## Reproduction

```c
#include <string.h>
void fill_t(unsigned char *dst) { memset(dst, 7, 4); }
```

Refused (`checked outcome simp search did not retain a complete proof`):

```click
import click::bytes;
verifying "ms0.c";
void fill_t(uint8* dst) {
    owns dst[0..4];
    ensures bytes::all_equal(dst, 0u64, 4u64, 7u8);
} by { execute(); simp(); }
```

Also refused: `ensures (0u64..4u64).all(|k| { dst[k] == 7u8 });` and the same
with `7`. Verifies: `ensures (0u64..4u64).all(|k| { defined(dst[k]) and dst[k] == 7u8 });`.
Adding `dst[4] = 0;` after the call (the original observation, 2026-10-16)
changes nothing; the store is not involved.

## Acceptance criteria

- `simp` derives a guarded universal from one whose body is a conjunction
  containing it, under identical guards, by a checked step that expands to
  source.
- Regression mdtest with the `memset` pattern above and the
  `bytes::all_equal` postcondition, plus a refusal where the dropped
  conjunct is not present (a body that only states `defined(..)`).
