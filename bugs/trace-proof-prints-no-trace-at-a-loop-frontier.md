# `--trace-proof` prints no trace when the failure is a loop frontier report

## Violated invariant

`click verify --trace-proof FUNCTION` shows the checked fact and resource
changes on the path to the failing tactic, and `--trace-to LINE` selects a
written tactic, "including in a successful proof; the tactic may sit inside a
proof `match` arm or a loop's `preserve` body"
(`docs/reference/cli/verify.md`). When the proof's failure is the
unfinished-`preserve` frontier report ("stopped inside the loop body ... the
frontier is at statement N"), the command prints that report and nothing
else: no `proof trace (checked tactics and branch facts):` section, with or
without `--trace-to`, and whichever tactic the line selects, including a
tactic before the loop.

Reproduced on `12a167a48` with a fixture already in the tree:

```sh
click verify --trace-proof scan mdtests/loop_preserve_frontier_report_multi_exit.md
click verify --trace-proof scan --trace-to 59 mdtests/loop_preserve_frontier_report_multi_exit.md
```

Both print the same eight lines as plain `click verify` on that file. The
same holds on the unfinished rbtree proof, whose README recommends the
command:

```sh
click verify --trace-proof __rb_insert --trace-to 1142 examples/rbtree-insert/rbtree_insert.frontier
```

(That frontier was finished and renamed `rbtree_insert.click` in rbtree
chunk 7; the multi-exit mdtest above still reproduces the bug.) Line 1142 is
a `fold` inside a finished proof `match` arm of the `preserve`
body; lines 1244 and 520 (a tactic before the loop) print no trace either.
For contrast, a proof that fails on an ordinary tactic inside `preserve`
prints the section
(`click verify --trace-proof spin mdtests/preserve_finished_arm_checked_before_frontier.md`).

The frontier report is the normal state of a long loop proof under
construction, which is exactly when a trace to a chosen tactic is wanted.

## Intended regression

A command-line test over `mdtests/loop_preserve_frontier_report_multi_exit.md`:
`--trace-proof scan --trace-to 59` prints a `proof trace` section that ends
at the selected `step()` in the `preserve` body and lists the `step` tactics
before it; `--trace-proof scan` without `--trace-to` prints the trace of the
path the frontier report names. A second case selects a tactic before the
`loop`.

## Acceptance criteria

- `--trace-proof` with a frontier-report failure prints the trace of the
  reported path, and `--trace-to` reaches any written tactic on a checked
  path of that proof, inside or outside the loop.
- If some selected tactic cannot be traced, the command says so and why,
  rather than printing the untraced error unchanged.
- The rbtree fixture README's recommended command prints a trace.
