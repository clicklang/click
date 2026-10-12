# Early-return completion still loses the whole-proof scaling bound

Reproduced on current master `0d2b58555` while rechecking the failures of
[nightly 38149193625](https://github.com/clicklang/click/actions/runs/38149193625).
The earlier report was removed in PR #702, but this regression still fails:

```sh
cargo nextest run --lib --profile nightly --run-ignored all \
  -E 'test(=surface::tests::scaling_tests::indexed_simp_premises_reduce_whole_early_return_work)'
```

The unchanged early-return fan-out verifies at all sizes. Whole-verification
deterministic work is 3,862 / 6,327 / 11,538 / 22,975 / 49,788 units for
4 / 8 / 16 / 32 / 64 returns. The last doubling grows by 2.1671x, exceeding
the existing 2.15x bound. This is not a wall-clock timeout.

The indexed premise selector remains within its bound; work accumulates in
completion and finishing. From 32 to 64 returns, `proof completion` grows from
3,626 to 11,274 units, `proof context finishing` from 6,593 to 16,897, and
`completion match` from 558 to 2,142. Contract certification currently scans
the claim's completed propositions to find a matching outcome for each path.
Further profiling is needed to attribute all superlinear completion work.

The companion `completed_early_return_contexts_are_reused_for_certification`
regression passes on this commit; that does not establish the tighter
whole-verification bound above.

Acceptance: preserve the original C and claims, make the existing multi-size
regression pass without relaxing its bounds, preserve false-postcondition
rejection and checked path identity, and cover any completion-index change
with deterministic scaling and relevant cross-path rejection cases.
