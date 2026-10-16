# A `transport using` refusal reports an available source as missing

Soundness: incomplete. A true claim is refused and the diagnostic is
misleading; nothing false is accepted, because the refusal comes from the
source-availability check before any frame decision.

## Violated invariant

The refusal "`transport using` requires a source derivable from its explicit
facts" prints a "missing pure fact" and then an "available pure facts" list
that contains the same fact up to the name of its quantifier's binder. Two
behaviours meet here:

- At a completed return outcome the source may name an exact result-path
  fact without being listed in `using` (`fact_transport.rs`,
  `available.contains(&source)`). That test is exact, not up to binder
  names, although a listed premise is accepted up to its binder's name
  (`listed_premise_available(.., true)`). A call postcondition is held with
  the binder its lowering chose, so the written source never matches it.
- Mid-execution, the source must be listed in `using`, and the refusal is
  correct in substance, but the printed "available pure facts" are the whole
  ambient set rather than the explicit facts the check reads, so the message
  shows the "missing" fact as available instead of saying to list it.

## Reproduction

```c
#include <string.h>
void fill_t(unsigned char *dst) { memset(dst, 7, 4); dst[4] = 0; }
```

Refused at the return outcome, with the source printed in the available list
(binder `<pointer C>` there, `<pointer A>` in the missing fact):

```click
verifying "ms.c";
void fill_t(uint8* dst) {
    owns dst[0..5];
    ensures (0u64..4u64).all(|k| { defined(dst[k]) and dst[k] == 7 });
} by {
    execute();
    transport(at(statement(1).entry, (0u64..4u64).all(|k| { defined(dst[k]) and dst[k] == 7 })),
              (0u64..4u64).all(|k| { defined(dst[k]) and dst[k] == 7 })) using { }
}
```

The same transport mid-execution (`step(); step();` then a `have` closed by
it) is refused the same way; listing the source in `using` verifies.

## Acceptance criteria

- At a return outcome, a source equal to an available fact up to binder
  names is accepted without being listed, as a listed premise would be.
- A mid-execution refusal names the source as available but not listed in
  `using` (or lists only the explicit facts it read), rather than printing
  it among the available facts as missing.
- Regression mdtests keep the `memset` then `dst[4] = 0` source.
