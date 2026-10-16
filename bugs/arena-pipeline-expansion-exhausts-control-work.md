# Arena pipeline expansion exhausts a quantified `have` control budget

Soundness: not soundness. The unchanged arena proof verifies, but expansion
cannot construct and check its explicit certificate within an existing control
work bound. No false acceptance is known.

Reproduced on `163709ed8` after the scalar-frame refusal repair (#1273), using
the current debug CLI:

```sh
click audit --claim arena_pipeline.contract examples/arena
```

The audit inventories 334 selected smart sites in `arena_pipeline.contract`.
Its original-sidecar session succeeds (16,290,482 deterministic units locally).
Whole-claim expansion then fails:

```text
`arena_pipeline.contract` tactic 48: `have` failed for
`forall (k: int32) { 0 <= k and k < arena->capacity implies arena->occupied[k] == 0 }`:
verification budget exhausted inside tactic `have` ...
after 2500001 units (2500000 limit; statement 17, source tactic 58)
location: tactic 58 > have body tactic 7 > have body tactic 9
```

This is the first zero-initialization claim after unfolding `o0` in
`examples/arena/arena_cells.click`, around line 2623. The original proof
introduces the index and bounds, instantiates the initialization postcondition,
and closes with `simp`. The failing atomic goal is a zero-valued memory read;
the diagnostic reports unsuccessful separation checks across call/read memory
snapshots. Do not infer a missing premise from those observations alone.

Collect operation attribution with `CLICK_TIMINGS=1` on the same audit command.
Diagnose the expensive checking path before changing search or expansion.
Preserve the existing C, proof claims, all 334 selected sites, and work bounds;
`--max-sites 1` does not exercise the whole-claim path.

Acceptance: the named whole-claim audit passes at unchanged limits, including
retained and cold rechecking and deterministic performance comparison. Add a
small deterministic multi-size regression preserving the identified repeated
work, and run the normal scaling controls for any representation change.
