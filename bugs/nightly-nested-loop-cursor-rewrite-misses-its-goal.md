# A nested-loop cursor `rewrite` misses the goal it was written for

Soundness: incomplete. Click refuses a `have` whose rewrite equality states the cursor's address in a different spelling from the goal. No false acceptance is known.

Priority: P2.

The inner loop's `preserve` proves `cursor == bytes + 4 * outer` with a
`rewrite` by `address(<pointer A>) == address(&bytes[4 * at(outer_head,
outer) + 4])`. The goal is `address(cursor) == address(bytes[(4 * outer)])`,
and the rewrite reports that its equality does not occur. Either the
equality's left side is no longer the cursor's spelling in the goal, or the
outer index is no longer written as `at(outer_head, outer)` there.

On master `071ed68b`, `click verify` gives byte-identical output with and
without the sequential-loop clause indexing (branch `seqloop3`). The fixture
still fails after rebasing onto master `ee00067b`. It is in `NIGHTLY` in
`tests/mdtests.rs`, so the gate does not run it.

```sh
MDTEST_FILTER=nested_loop_cursor_view_authority RUST_MIN_STACK=8388608 \
  cargo nextest run --test mdtests
```

```text
expected pass, but failed: `f.contract` tactic 2 (`loop`), `preserve` tactic 26: `have` failed for `cursor == (bytes + (4 * outer))`: `f.contract` proof step tactic 35 > have body tactic 3: `rewrite`  …
error kind: proof error
tactic: rewrite
stage: proof step
location: tactic 35 > have body tactic 3
equality: address(<pointer A>) == address(&bytes[4 * at(outer_head, outer) + 4])
goal: address(cursor) == address(bytes[(4 * outer)])
recent premises (showing 8 of 28):
cursor == (bytes[(4 * outer)])
address(<pointer A>) == address(&bytes[4 * at(outer_head, outer) + 4])
true
4 * (at(outer_head, outer) + 1) == 4 * at(outer_head, outer) + 4
```

Invariant: a rewrite by an equality between pointer addresses applies where the goal names the same pointer, under the spelling the proof's earlier steps established.

Acceptance: the fixture passes unchanged. A gate regression keeps the nested cursor pattern.
