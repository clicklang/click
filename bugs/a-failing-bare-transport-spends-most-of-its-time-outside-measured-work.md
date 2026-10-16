# A failing bare `transport` spends most of its time outside measured work

Soundness: not soundness. This is a performance defect on a refusal path.
The claim refused is false, and the refusal is correct; only the time it
takes is at fault.

## Violated invariant

A refused simple-shaped proof step should fail promptly, with its cost
visible in deterministic work and attributed to measured operations
(`docs/internals/testing.md`, `docs/internals/verification-efficiency.md`).
A failing bare `transport(at(mark, F), F)` instead takes about twice as long
as the same transport written with `using { at(mark, F); }`, and most of the
difference falls outside every measured operation. CLAUDE.md treats
unexpected slowness as a tooling defect.

Measured on a debug build at `70fb09fd` (4-core cloud container):

- The bare `transport` tactic: about 0.53 s and 47,248 work units
  (`CLICK_TIMINGS=1`, `class smart`). The whole fixture verifies in about
  0.8 s. The baseline before `70fb09fd` measured the same, about 0.8 s and
  547 ms SMART in `click profile`, so the cost predates that change.
- The same transport with its source listed in `using`: about 0.35 s for the
  whole fixture.
- Summing `CLICK_TIMINGS` operation lines for the bare run accounts for about
  200 ms: `explicit fact transport: quantified frame` 66 ms and 12,055 units
  (one call), `verification statement: call` 29 ms, `atomic dependency
  indexing` 29 ms (819 calls), `explicit fact transport: premise check`
  27 ms and 941 units (two calls). About 330 ms of the tactic is in no
  measured operation.

A bare `transport` runs `try_execution_fact_transport`, which checks
`transport using` with an empty list and then with the source alone (the
quantified frame runs here and refuses). It then runs the premise planner
`plan_explicit_fact_transport`
(`src/surface/proof/fixed_state_proofs/fact_transport.rs`), which
synthesizes a surface form for every available fact
(`checked_surface_comparison_fact_in_state`), checks the complete candidate
list, and renders its own refusal. Which of these holds the unmeasured time
has not been established; the candidate synthesis and the repeated refusal
rendering are uncharged and unmeasured, so they are the first suspects.

The planner's own check (`check_premises`, ending in
`certified_fact_transport_reaches`) never tries the quantified frame or the
fold read frame, which the explicit `transport using` check does. So the
planner can spend its time on premise selection for a transport whose only
missing evidence is a frame its check cannot ask about, and a bare transport
can be refused where planned premises plus the frame would carry it.

## Reproduction

`mdtests/bare_transport_names_its_uncarried_leaf.md`:

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

Time it with `CLICK_TIMINGS=1 click verify` on that file, and compare it
with the same proof with `using { at(filled, ...); }` added to the transport.

## Acceptance criteria

- The failing bare `transport` is prompt: its time is attributed to measured
  operations, and its cost is close to that of the explicit `using` form
  plus work proportional to the candidates the planner actually checks.
- `mdtests/bare_transport_names_its_uncarried_leaf.md` runs under half a
  second in the gate, and its entry is removed from `NIGHTLY` in
  `tests/mdtests.rs`.
- Either the planner's premise check consults the same frames as the
  explicit `transport using` check, or the reason it does not is documented
  beside `plan_explicit_fact_transport`.
