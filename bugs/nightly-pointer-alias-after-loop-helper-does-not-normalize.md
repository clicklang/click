# A field alias after a loop helper does not normalize

Soundness: incomplete. Click refuses `identity->right == q->right` after a loop, although the loop's frame leaves both reads unchanged. No false acceptance is known.

Priority: P2.

In `inspect`'s loop `preserve`, `have identity->right == q->right` fails at
`normalize using`: the goal is `at(<state A>, *((char *)identity + 8)) ==
at(<state B>, q[2])`. The premises relate `*identity` to `p[0]` and `q[0]`,
but nothing relates the byte-offset read `*((char *)identity + 8)` to the
field read `q[2]`. The alias is known for the base field and not carried to
the field at offset 8.

On master `071ed68b`, `click verify` gives byte-identical output with and
without the sequential-loop clause indexing (branch `seqloop3`). The fixture
still fails after rebasing onto master `ee00067b`. It is in `NIGHTLY` in
`tests/mdtests.rs`, so the gate does not run it.

```sh
MDTEST_FILTER=pointer_read_alias_after_loop_helper RUST_MIN_STACK=8388608 \
  cargo nextest run --test mdtests
```

```text
expected pass, but failed: `inspect.contract` tactic 1 (`loop`), `preserve` tactic 14: `have` failed for `identity->right == q->right`: `inspect.contract` proof step tactic 17 > have body tactic 1: `n …
error kind: proof error
tactic: normalize()
stage: proof step
location: tactic 17 > have body tactic 1
goal: at(<state A>, *((char *)identity + 8)) == at(<state B>, q[2])
recent premises (showing 8 of 23):
<2 written range(s) between `statement(4).exit` and here>
at(<state A>, *identity) == at(<state B>, p[0])
at(<state A>, *identity) == at(<state A>, q[0])
q == q
viewable(q[2..4])
```

Invariant: an alias between two struct pointers lets a later field read through one be compared with the same field read through the other.

Acceptance: the fixture passes unchanged. A gate regression keeps the helper-then-loop alias pattern.
