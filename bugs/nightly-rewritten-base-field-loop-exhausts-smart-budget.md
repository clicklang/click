# A loop over a rewritten base field exhausts its smart budget instead of refusing

Soundness: not soundness. The program is still rejected, but the diagnostic is wrong: the fixture expects the refusal that names the unproved invariant obligation, and gets the smart budget's exhaustion instead.

Priority: P2.

The fixture expects `closure body did not prove every invariant
obligation`. `close_invariants` in `mark_and_swap.contract` instead stops at
the unresolved obligation `... arena->occupied == at(loop(0).entry,
arena->occupied)` after exhausting its deterministic smart work budget of 2,000,000
units, after 18 s in a debug build. The obligation is false, because the
body rewrites `arena->occupied`. A bounded smart search should report it
promptly as unproved rather than exhaust its budget.

On master `071ed68b`, `click verify` gives byte-identical output with and
without the sequential-loop clause indexing (branch `seqloop3`). The fixture
still fails after rebasing onto master `ee00067b`. It is in `NIGHTLY` in
`tests/mdtests.rs`, so the gate does not run it.

```sh
MDTEST_FILTER=loop_frame_rejects_rewritten_base_field RUST_MIN_STACK=8388608 \
  cargo nextest run --test mdtests
```

```text
expected failure containing `closure body did not prove every invariant obligation`, got `; this loop declares `decreases`, so the bundle also has `0 <= end - i` at the back edge, `end - i` decreases  …
named-operation attribution was not collected; rerun under `click profile` or with CLICK_TIMINGS=1 to see where the units went; smart search is heuristic, so try a smaller smart tactic or explicit sim …
stage: proof step
location: tactic 6
goal: start <= at(statement(3).entry, i) + 1 and ((start <= at(statement(3).entry, i) + 1 implies at(statement(3).entry, i) + 1 <= end) and ((start <= at(statement(3).entry, i) + 1 implies at(statemen …
recent premises (showing 8 of 30):
<only arena[0] changed between `statement(3).entry` and `statement(3).exit`>
forall (k: int32) { 0 <= k and k < start implies at(<state A>, *<pointer C>) == old(*<pointer B>) }
<3 written range(s) between `statement(1).exit` and `statement(3).entry`>
at(<state A>, arena[0]) == old(arena[0])
at(statement(3).entry, i) <= end
end <= at(<state A>, arena[4])
```

Invariant: a smart closer that meets a false invariant obligation refuses it with the documented message within a small part of its budget.

Acceptance: the fixture gets its expected message. No budget or threshold is raised.
