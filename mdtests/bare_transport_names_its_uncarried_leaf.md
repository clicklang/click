# A bare `transport` refusal names the leaf its frame could not carry

`dst[3] = 0` overwrites one of the cells `memset` set to `7`, so the claim
that all four still hold `7` is false and the bare `transport` is refused.
Its premise planner selects nothing that carries the source, and its refusal
is the one the same transport gets with its source listed in `using`: the
quantified frame's refusal, naming the value read it could not carry, the
states it compared (the `memset` exit and the state after the store), and the
store to `dst[3]` among the effects between them.

```c filename=fill.c
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

```expect
fail: quantified frame: a leaf was not carried: a read in it was not shown unchanged between its two snapshots by the steps between them and this context's facts
  leaf it had: at(<state A>, dst[k]) == 7
  leaf it wanted: at(<state B>, dst[k]) == 7
  where
    <state A> is `statement(1).entry`, projected for one read
    <state B> is this state, projected for one read
  this is the refusal with the source as the only premise; no other available fact the premise planner could list carried it either
```
