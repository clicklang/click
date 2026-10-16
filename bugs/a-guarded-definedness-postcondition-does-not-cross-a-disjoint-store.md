# A guarded definedness postcondition does not cross a disjoint store

Soundness: incomplete. A true claim is refused; nothing false is accepted,
because the refusal comes from `simp` and `transport` finding no derivation.

## Violated invariant

A store that writes only cells outside a quantified fact's range leaves the
fact true. After `memset(dst, 7, 4); dst[4] = 0;`, `memset`'s own
postcondition `(0u64..4u64).all(|k| { defined(dst[k]) and dst[k] == 7 })`
still holds at exit, and the trace records `only dst[4] changed` between the
call and the exit. `execute(); simp();` refuses it. The same fact without
the `defined(..)` conjunct, proved by a `have` right after the call, is
carried to the exit by `simp` (it expands to
`transport(at(statement(1).entry, F), F) using { }`), so the frame works for
the value conjunct but not for the definedness atom.

An explicit `transport(at(statement(1).entry, F), F) using { }` with the
`defined(..) and` form is refused with "requires a source derivable from its
explicit facts", although the printed available facts contain the source
spelled identically. With a `mark filled;` after the call,
`transport(at(filled, F), F)` is refused for both forms with "could not make
fact transport premises explicit" while reporting the checked source holds.

Found while fixing `simp-cannot-drop-a-conjunct-under-a-quantified-guard`
(2026-10-16); that bug's report said the store was not involved, but its
original program (`memset` followed by `dst[4] = 0`) still fails for this
reason after the fix.

## Reproduction

```c
#include <string.h>
void fill_t(unsigned char *dst) { memset(dst, 7, 4); dst[4] = 0; }
```

Refused (`checked outcome simp search did not retain a complete proof`):

```click
verifying "ms.c";
void fill_t(uint8* dst) {
    owns dst[0..5];
    ensures (0u64..4u64).all(|k| { defined(dst[k]) and dst[k] == 7 });
} by { execute(); simp(); }
```

Also refused, the original observation:

```click
import click::bytes;
verifying "ms.c";
void fill_t(uint8* dst) {
    owns dst[0..5];
    ensures bytes::all_equal(dst, 0u64, 4u64, 7u8);
} by { execute(); simp(); }
```

Verifies: the same program with `step(); have (0u64..4u64).all(|k| { dst[k] == 7 }); step(); execute(); simp();`.

## Acceptance criteria

- Both claims above verify with `execute(); simp();`, and expansion prints a
  checked transport that re-verifies.
- An explicit `transport` of the `defined(..) and` form across the store is
  accepted, or its refusal names the missing frame evidence.
- Regression mdtests keep the `memset` then `dst[4] = 0` source, plus a
  refusal where the store writes a cell inside the quantified range.
