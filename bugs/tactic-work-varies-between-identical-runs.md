# Tactic work varies between identical runs

Soundness: not soundness. Repeated identical runs charge a tactic slightly
different work. Nothing false verifies, but a proof near its budget could
pass one run and fail the next.

Verdicts are meant to be deterministic: "the same source spends the same
units on any machine under any load" (`click verify --help`). Running the
same command several times, with the same binary and the same files, gives
different work for some of `arena_pipeline`'s control tactics.

## Reproduction

```sh
cargo build --release --bin click
for i in 1 2 3; do
  CLICK_TIMINGS=1 target/release/click verify examples/arena/arena_cells.click:4445:5 2>&1 |
    grep -o 'arena_pipeline.contract \(48\|308\) have class control .* work [0-9]*'
done
```

On master at filing, line 4445 is `arena_pipeline`'s second `have forall
(k: int32) { 0 <= k and k < arena->capacity implies arena->occupied[k] == 0
}`; any location in `arena_pipeline` selects the same unit. The control
`have` at statement 17, source tactic 58 spent 232,038, 231,067 and 230,232
units in three runs. The one at statement 35, source tactic 347 spent
193,346, 195,516 and 193,369. Of the unit's 347 tactics, 31 differed between
two runs, by about 1% each. Small sidecars (`examples/linked-list`, a
nine-function generated fixture) repeat exactly, so it shows only in larger
proofs.

The cause is not established. Candidates are iteration over a hash table
seeded per process (`std::collections::HashMap` with the default hasher), and
caches keyed by memory addresses, which change from one process to the next.

## Intended regression

A gate test that verifies one moderately large unit twice in separate
processes, or with each process-level seed changed, and asserts that each
tactic's work is identical.

## Acceptance criteria

- The command above reports the same work for every tactic in every run.
- The cause is named, and nothing a run's charged work depends on comes from
  process-specific hashing or addresses.
