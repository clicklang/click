# A bare `transport` frame refusal does not name the uncarried read

Soundness: sound. The claim refused is false; only the diagnostic is at
fault.

## Violated invariant

A bare `transport(at(mark, F), F)` (no `using`) plans its premises and, when
the checked quantified frame refuses, reports
"could not make fact transport premises explicit: explicit surface premises
do not view the certified fact transport" with the checked source and target.
It names neither the condition or `defined(..)` leaf the frame could not
carry nor the store it could not separate. The same transport written with
`using { at(mark, F); }` reports "found no frame evidence carrying its source
fact to the target's state" with the cell walks it performed. The planner
should surface the frame's refusal (`QuantifiedFrameRefusal::LeafNotCarried`
keeps both sides) instead of describing it as a premise-selection failure.

## Reproduction

```c
#include <string.h>
void fill(unsigned char *dst) { memset(dst, 7, 4); dst[3] = 0; }
```

```click
verifying "fill.c";
void fill(uint8* dst) {
    owns dst[0..4];
    ensures (0u64..4u64).all(|k| { defined(dst[k]) and dst[k] == 7 });
} by {
    step();
    mark filled;
    step();
    transport(at(filled, (0u64..4u64).all(|k| { defined(dst[k]) and dst[k] == 7 })),
              (0u64..4u64).all(|k| { defined(dst[k]) and dst[k] == 7 }));
}
```

Adding `using { at(filled, ...); }` with the same source gives the
"found no frame evidence" refusal, which names the cell walks;
`mdtests/a_guarded_memset_postcondition_does_not_cross_a_store_of_unknown_separation.md`
is a regression of that `using` form.

## Acceptance criteria

- The bare form's refusal names the frame evidence it lacked (the leaf and
  the store not shown separate), as the `using` form does.
- A regression mdtest of the bare form expects that text.
