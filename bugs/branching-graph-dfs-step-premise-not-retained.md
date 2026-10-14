# `branching_graph_dfs` step evidence needs a premise the proof dropped

The nightly mdtest `mdtests/branching_graph_dfs.md` fails on master
`d7501d30f`:

```sh
MDTEST_FILTER=branching_graph_dfs CLICK_NIGHTLY=1 cargo test --release --test mdtests
```

```text
expected pass, but failed: `dfs.contract` tactic 25: `step()` recorded statement
evidence the proof object rejected: evidence assumes a premise the proof did not
retain; the premise is 0 <= old(left[cur])
```

The mdtest is listed in `NIGHTLY` in `tests/mdtests.rs` (6.2 s), so the gate
does not run it. The most recent change to the file is `52553ca05`. The
breaking commit is not yet bisected.

The broken invariants:
- A `step()` that succeeds records evidence the proof object accepts. Here
  the step derived `0 <= old(left[cur])` while checking and then emitted
  evidence that assumes it without retaining it, which is the hidden-
  prerequisite gap the census ratchets count.
- The whole-corpus mdtests census cannot be checked while this fails: the
  ratchet runs only after every mdtest passes.

Acceptance:
- `branching_graph_dfs` verifies again, with the premise either retained by
  the step that derives it or stated in the proof, and the C unchanged.
- A small gate mdtest has a `step()` whose evidence needs a bound read from
  an `old(...)` array cell, and shows the step's evidence is accepted.
