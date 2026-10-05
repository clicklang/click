# Expanding one smart site in `__rb_insert` exhausts memory

## Violated invariant

Expansion must not cost far more than the verification it retraces, and a
tactic that cannot finish fails promptly within its deterministic work budget
(`AGENTS.md`, "Tooling stability comes first" and "Scalable verification is a
correctness requirement"). Counted work is meant to bound time and memory.

`click audit` on `examples/rbtree-insert/rbtree_insert.click` does neither at
the first smart site of `__rb_insert.contract`. Verifying the whole sidecar
takes about 31 seconds and about 5 GB at its peak. Expanding that one site
then allocates without bound. Uncapped, it took a 31 GB machine out of memory
twice on 2026-10-03, once killing the session that ran it. No site of the
claim ever finished, so the growth is inside one expansion, not accumulated
across the claim's 190 sites.

## Reproduction

Run it only under a hard memory cap. On a release build:

```sh
cd examples
systemd-run --user --scope -q -p MemoryMax=8G -p MemorySwapMax=0 \
    ../target/release/click audit --verbose \
    --start-at rbtree-insert/rbtree_insert.click:LINE:1 \
    rbtree-insert/rbtree_insert.click
```

`LINE` is the line of `void __rb_insert(`. The first site audited is the
proof's first smart tactic, `have parent == node_parent by { simp(); }`,
before the loop. Measured resident memory, sampled every 10 seconds from
process start:

| elapsed | resident memory | sites finished |
| --- | --- | --- |
| 40 s | 0.2 GB | 0 |
| 70 s | 2.3 GB | 0 |
| 90 s | 5.2 GB | 0 |
| 110 s | 7.9 GB | 0 |

The session reports ready after about 31 seconds and 15.3 million units, at
low memory. Growth then runs at about 2.7 GB per 20 seconds until the cap
kills the process (exit 137). The default `--expansion-work-limit` of 50
million units does not stop it first.

The same run on `844511606`, before user-defined tactics and before
`__rb_insert`'s root-form contract, follows the same curve (6.9 GB at 100
seconds, killed at the cap), so neither change introduced it.

The smaller claims of the same sidecar audit normally in the same session:
the eight claims before `__rb_insert.contract` passed in both uncapped runs.

Not investigated: which phase allocates (generating the expansion, the
retained-session verification of the rewritten proof, or the cold targeted
one), and whether `click expand` on the single site reproduces it without the
audit.

## Intended regression

A deterministic scaling regression that expands one early smart site of a
proof whose remaining script is large (many `match` arms after the site), at
several sizes, and asserts the expansion's counted work and allocation stay
within a constant factor of verifying the same proof. Then the reproduction
above finishing under the cap.

## Acceptance criteria

- Auditing `examples/rbtree-insert` completes within a small multiple of its
  verification's peak memory.
- An expansion that cannot finish stops at its work budget with a local
  diagnostic, before memory grows without bound.
- `scripts/check.sh` passes.
